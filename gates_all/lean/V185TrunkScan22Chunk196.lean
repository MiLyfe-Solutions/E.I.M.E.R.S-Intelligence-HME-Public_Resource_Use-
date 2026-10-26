import V185TrunkScan22Chunk195

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1747160 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_1747160 : Nat := 118140960795 + 1747160 * 2 ^ 59
def prefixEnd_1747160 : Nat := 4983230072969 + 3 ^ 40 * 1747160 * 2
def baseEnd_1747160 : Nat := 598088573539659641443309

theorem tailTrace_1747160 : CollatzResearch.WordTrace tailWord_1747160 prefixEnd_1747160 598088573539659641443309 := by
  unfold tailWord_1747160
  simp only [CollatzResearch.WordTrace]
  refine ⟨31862080175172593008487467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42482773566896790677983289 31862080175172593008487467)
  ·
    refine ⟨47793120262758889512731201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31862080175172593008487467 47793120262758889512731201)
    ·
      refine ⟨35844840197069167134548401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47793120262758889512731201 35844840197069167134548401)
      ·
        refine ⟨26883630147801875350911301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35844840197069167134548401 26883630147801875350911301)
        ·
          refine ⟨5040680652712851628295869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26883630147801875350911301 5040680652712851628295869)
          ·
            refine ⟨1890255244767319360610951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5040680652712851628295869 1890255244767319360610951)
            ·
              refine ⟨2835382867150979040916427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890255244767319360610951 2835382867150979040916427)
              ·
                refine ⟨4253074300726468561374641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835382867150979040916427 4253074300726468561374641)
                ·
                  refine ⟨3189805725544851421030981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4253074300726468561374641 3189805725544851421030981)
                  ·
                    refine ⟨598088573539659641443309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3189805725544851421030981 598088573539659641443309)
                    ·
                      rfl

theorem cell22_1747160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_1747160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747160 prefixEnd_1747160 := by exact prefixLift 1747160
  have htrace : WordTrace (prefixWord ++ tailWord_1747160) baseStart_1747160 baseEnd_1747160 := by
    simpa [prefixWord, tailWord_1747160, baseEnd_1747160] using wordTrace_append hprefix tailTrace_1747160
  have hstable : (prefixWord ++ tailWord_1747160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747160).length < 2 ^ (prefixWord ++ tailWord_1747160).sum := by decide
  have hdescent : baseEnd_1747160 < baseStart_1747160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747164 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_1747164 : Nat := 118140960795 + 1747164 * 2 ^ 59
def prefixEnd_1747164 : Nat := 4983230072969 + 3 ^ 40 * 1747164 * 2
def baseEnd_1747164 : Nat := 199363314273801654781099

theorem tailTrace_1747164 : CollatzResearch.WordTrace tailWord_1747164 prefixEnd_1747164 199363314273801654781099 := by
  unfold tailWord_1747164
  simp only [CollatzResearch.WordTrace]
  refine ⟨31862153121165347350060273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42482870828220463133413697 31862153121165347350060273)
  ·
    refine ⟨23896614840874010512545205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31862153121165347350060273 23896614840874010512545205)
    ·
      refine ⟨2240307641331938485551113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23896614840874010512545205 2240307641331938485551113)
      ·
        refine ⟨1680230730998953864163335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240307641331938485551113 1680230730998953864163335)
        ·
          refine ⟨2520346096498430796245003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680230730998953864163335 2520346096498430796245003)
          ·
            refine ⟨3780519144747646194367505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520346096498430796245003 3780519144747646194367505)
            ·
              refine ⟨2835389358560734645775629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780519144747646194367505 2835389358560734645775629)
              ·
                refine ⟨1063271009460275492165861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835389358560734645775629 1063271009460275492165861)
                ·
                  refine ⟨199363314273801654781099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063271009460275492165861 199363314273801654781099)
                  ·
                    rfl

theorem cell22_1747164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_1747164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747164 prefixEnd_1747164 := by exact prefixLift 1747164
  have htrace : WordTrace (prefixWord ++ tailWord_1747164) baseStart_1747164 baseEnd_1747164 := by
    simpa [prefixWord, tailWord_1747164, baseEnd_1747164] using wordTrace_append hprefix tailTrace_1747164
  have hstable : (prefixWord ++ tailWord_1747164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747164).length < 2 ^ (prefixWord ++ tailWord_1747164).sum := by decide
  have hdescent : baseEnd_1747164 < baseStart_1747164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747190 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1747190 : Nat := 118140960795 + 1747190 * 2 ^ 59
def prefixEnd_1747190 : Nat := 4983230072969 + 3 ^ 40 * 1747190 * 2
def baseEnd_1747190 : Nat := 598098843152749563193217

theorem tailTrace_1747190 : CollatzResearch.WordTrace tailWord_1747190 prefixEnd_1747190 598098843152749563193217 := by
  unfold tailWord_1747190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982828408764781321285439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42483503026824334093711349 3982828408764781321285439)
  ·
    refine ⟨5974242613147171981928159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3982828408764781321285439 5974242613147171981928159)
    ·
      refine ⟨8961363919720757972892239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974242613147171981928159 8961363919720757972892239)
      ·
        refine ⟨13442045879581136959338359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961363919720757972892239 13442045879581136959338359)
        ·
          refine ⟨20163068819371705439007539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442045879581136959338359 20163068819371705439007539)
          ·
            refine ⟨30244603229057558158511309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20163068819371705439007539 30244603229057558158511309)
            ·
              refine ⟨11341726210896584309441741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30244603229057558158511309 11341726210896584309441741)
              ·
                refine ⟨4253147329086219116040653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11341726210896584309441741 4253147329086219116040653)
                ·
                  refine ⟨1594930248407332168515245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4253147329086219116040653 1594930248407332168515245)
                  ·
                    refine ⟨598098843152749563193217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1594930248407332168515245 598098843152749563193217)
                    ·
                      rfl

theorem cell22_1747190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1747190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747190 prefixEnd_1747190 := by exact prefixLift 1747190
  have htrace : WordTrace (prefixWord ++ tailWord_1747190) baseStart_1747190 baseEnd_1747190 := by
    simpa [prefixWord, tailWord_1747190, baseEnd_1747190] using wordTrace_append hprefix tailTrace_1747190
  have hstable : (prefixWord ++ tailWord_1747190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747190).length < 2 ^ (prefixWord ++ tailWord_1747190).sum := by decide
  have hdescent : baseEnd_1747190 < baseStart_1747190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747263 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_1747263 : Nat := 118140960795 + 1747263 * 2 ^ 59
def prefixEnd_1747263 : Nat := 4983230072969 + 3 ^ 40 * 1747263 * 2
def baseEnd_1747263 : Nat := 598123832544601706117993

theorem tailTrace_1747263 : CollatzResearch.WordTrace tailWord_1747263 prefixEnd_1747263 598123832544601706117993 := by
  unfold tailWord_1747263
  simp only [CollatzResearch.WordTrace]
  refine ⟨63727917068972034607974443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42485278045981356405316295 63727917068972034607974443)
  ·
    refine ⟨95591875603458051911961665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63727917068972034607974443 95591875603458051911961665)
    ·
      refine ⟨71693906702593538933971249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95591875603458051911961665 71693906702593538933971249)
      ·
        refine ⟨53770430026945154200478437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71693906702593538933971249 53770430026945154200478437)
        ·
          refine ⟨10081955630052216412589707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53770430026945154200478437 10081955630052216412589707)
          ·
            refine ⟨15122933445078324618884561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081955630052216412589707 15122933445078324618884561)
            ·
              refine ⟨11342200083808743464163421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15122933445078324618884561 11342200083808743464163421)
              ·
                refine ⟨4253325031428278799061283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11342200083808743464163421 4253325031428278799061283)
                ·
                  refine ⟨6379987547142418198591925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253325031428278799061283 6379987547142418198591925)
                  ·
                    refine ⟨598123832544601706117993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6379987547142418198591925 598123832544601706117993)
                    ·
                      rfl

theorem cell22_1747263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_1747263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747263 prefixEnd_1747263 := by exact prefixLift 1747263
  have htrace : WordTrace (prefixWord ++ tailWord_1747263) baseStart_1747263 baseEnd_1747263 := by
    simpa [prefixWord, tailWord_1747263, baseEnd_1747263] using wordTrace_append hprefix tailTrace_1747263
  have hstable : (prefixWord ++ tailWord_1747263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747263).length < 2 ^ (prefixWord ++ tailWord_1747263).sum := by decide
  have hdescent : baseEnd_1747263 < baseStart_1747263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747325 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_1747325 : Nat := 118140960795 + 1747325 * 2 ^ 59
def prefixEnd_1747325 : Nat := 4983230072969 + 3 ^ 40 * 1747325 * 2
def baseEnd_1747325 : Nat := 598145056411654211067803

theorem tailTrace_1747325 : CollatzResearch.WordTrace tailWord_1747325 prefixEnd_1747325 598145056411654211067803 := by
  unfold tailWord_1747325
  simp only [CollatzResearch.WordTrace]
  refine ⟨63730178394747419196731429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42486785596498279464487619 63730178394747419196731429)
  ·
    refine ⟨11949408449015141099387143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63730178394747419196731429 11949408449015141099387143)
    ·
      refine ⟨17924112673522711649080715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11949408449015141099387143 17924112673522711649080715)
      ·
        refine ⟨26886169010284067473621073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17924112673522711649080715 26886169010284067473621073)
        ·
          refine ⟨20164626757713050605215805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26886169010284067473621073 20164626757713050605215805)
          ·
            refine ⟨7561735034142393976955927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20164626757713050605215805 7561735034142393976955927)
            ·
              refine ⟨11342602551213590965433891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7561735034142393976955927 11342602551213590965433891)
              ·
                refine ⟨17013903826820386448150837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342602551213590965433891 17013903826820386448150837)
                ·
                  refine ⟨1595053483764411229514141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17013903826820386448150837 1595053483764411229514141)
                  ·
                    refine ⟨598145056411654211067803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595053483764411229514141 598145056411654211067803)
                    ·
                      rfl

theorem cell22_1747325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_1747325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747325 prefixEnd_1747325 := by exact prefixLift 1747325
  have htrace : WordTrace (prefixWord ++ tailWord_1747325) baseStart_1747325 baseEnd_1747325 := by
    simpa [prefixWord, tailWord_1747325, baseEnd_1747325] using wordTrace_append hprefix tailTrace_1747325
  have hstable : (prefixWord ++ tailWord_1747325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747325).length < 2 ^ (prefixWord ++ tailWord_1747325).sum := by decide
  have hdescent : baseEnd_1747325 < baseStart_1747325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747353 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1747353 : Nat := 118140960795 + 1747353 * 2 ^ 59
def prefixEnd_1747353 : Nat := 4983230072969 + 3 ^ 40 * 1747353 * 2
def baseEnd_1747353 : Nat := 598154641383871471367717

theorem tailTrace_1747353 : CollatzResearch.WordTrace tailWord_1747353 prefixEnd_1747353 598154641383871471367717 := by
  unfold tailWord_1747353
  simp only [CollatzResearch.WordTrace]
  refine ⟨63731199638645979978750713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42487466425763986652500475 63731199638645979978750713)
  ·
    refine ⟨47798399728984484984063035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63731199638645979978750713 47798399728984484984063035)
    ·
      refine ⟨71697599593476727476094553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47798399728984484984063035 71697599593476727476094553)
      ·
        refine ⟨53773199695107545607070915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71697599593476727476094553 53773199695107545607070915)
        ·
          refine ⟨80659799542661318410606373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53773199695107545607070915 80659799542661318410606373)
          ·
            refine ⟨15123712414248997201988695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80659799542661318410606373 15123712414248997201988695)
            ·
              refine ⟨22685568621373495802983043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123712414248997201988695 22685568621373495802983043)
              ·
                refine ⟨34028352932060243704474565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22685568621373495802983043 34028352932060243704474565)
                ·
                  refine ⟨6380316174761295694588981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34028352932060243704474565 6380316174761295694588981)
                  ·
                    refine ⟨598154641383871471367717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6380316174761295694588981 598154641383871471367717)
                    ·
                      rfl

theorem cell22_1747353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1747353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747353 prefixEnd_1747353 := by exact prefixLift 1747353
  have htrace : WordTrace (prefixWord ++ tailWord_1747353) baseStart_1747353 baseEnd_1747353 := by
    simpa [prefixWord, tailWord_1747353, baseEnd_1747353] using wordTrace_append hprefix tailTrace_1747353
  have hstable : (prefixWord ++ tailWord_1747353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747353).length < 2 ^ (prefixWord ++ tailWord_1747353).sum := by decide
  have hdescent : baseEnd_1747353 < baseStart_1747353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747477 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1747477 : Nat := 118140960795 + 1747477 * 2 ^ 59
def prefixEnd_1747477 : Nat := 4983230072969 + 3 ^ 40 * 1747477 * 2
def baseEnd_1747477 : Nat := 598197089117976481267337

theorem tailTrace_1747477 : CollatzResearch.WordTrace tailWord_1747477 prefixEnd_1747477 598197089117976481267337 := by
  unfold tailWord_1747477
  simp only [CollatzResearch.WordTrace]
  refine ⟨63735722290196749156264685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42490481526797832770843123 63735722290196749156264685)
  ·
    refine ⟨23900895858823780933599257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63735722290196749156264685 23900895858823780933599257)
    ·
      refine ⟨17925671894117835700199443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23900895858823780933599257 17925671894117835700199443)
      ·
        refine ⟨26888507841176753550299165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17925671894117835700199443 26888507841176753550299165)
        ·
          refine ⟨10083190440441282581362187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26888507841176753550299165 10083190440441282581362187)
          ·
            refine ⟨15124785660661923872043281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10083190440441282581362187 15124785660661923872043281)
            ·
              refine ⟨11343589245496442904032461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15124785660661923872043281 11343589245496442904032461)
              ·
                refine ⟨4253845967061166089012173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11343589245496442904032461 4253845967061166089012173)
                ·
                  refine ⟨1595192237647937283379565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4253845967061166089012173 1595192237647937283379565)
                  ·
                    refine ⟨598197089117976481267337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595192237647937283379565 598197089117976481267337)
                    ·
                      rfl

theorem cell22_1747477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1747477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747477 prefixEnd_1747477 := by exact prefixLift 1747477
  have htrace : WordTrace (prefixWord ++ tailWord_1747477) baseStart_1747477 baseEnd_1747477 := by
    simpa [prefixWord, tailWord_1747477, baseEnd_1747477] using wordTrace_append hprefix tailTrace_1747477
  have hstable : (prefixWord ++ tailWord_1747477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747477).length < 2 ^ (prefixWord ++ tailWord_1747477).sum := by decide
  have hdescent : baseEnd_1747477 < baseStart_1747477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747479 : List Nat := [1, 1, 3, 6, 1, 2, 1, 7]
def baseStart_1747479 : Nat := 118140960795 + 1747479 * 2 ^ 59
def prefixEnd_1747479 : Nat := 4983230072969 + 3 ^ 40 * 1747479 * 2
def baseEnd_1747479 : Nat := 66466419306538793635259

theorem tailTrace_1747479 : CollatzResearch.WordTrace tailWord_1747479 prefixEnd_1747479 66466419306538793635259 := by
  unfold tailWord_1747479
  simp only [CollatzResearch.WordTrace]
  refine ⟨63735795236189503497837491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42490530157459668998558327 63735795236189503497837491)
  ·
    refine ⟨95603692854284255246756237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63735795236189503497837491 95603692854284255246756237)
    ·
      refine ⟨35851384820356595717533589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95603692854284255246756237 35851384820356595717533589)
      ·
        refine ⟨1680533663454215424259387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35851384820356595717533589 1680533663454215424259387)
        ·
          refine ⟨2520800495181323136389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680533663454215424259387 2520800495181323136389081)
          ·
            refine ⟨1890600371385992352291811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520800495181323136389081 1890600371385992352291811)
            ·
              refine ⟨2835900557078988528437717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890600371385992352291811 2835900557078988528437717)
              ·
                refine ⟨66466419306538793635259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2835900557078988528437717 66466419306538793635259)
                ·
                  rfl

theorem cell22_1747479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 7].length) (baseStart_1747479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747479 prefixEnd_1747479 := by exact prefixLift 1747479
  have htrace : WordTrace (prefixWord ++ tailWord_1747479) baseStart_1747479 baseEnd_1747479 := by
    simpa [prefixWord, tailWord_1747479, baseEnd_1747479] using wordTrace_append hprefix tailTrace_1747479
  have hstable : (prefixWord ++ tailWord_1747479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747479).length < 2 ^ (prefixWord ++ tailWord_1747479).sum := by decide
  have hdescent : baseEnd_1747479 < baseStart_1747479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747490 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1747490 : Nat := 118140960795 + 1747490 * 2 ^ 59
def prefixEnd_1747490 : Nat := 4983230072969 + 3 ^ 40 * 1747490 * 2
def baseEnd_1747490 : Nat := 199400513094549593564099

theorem tailTrace_1747490 : CollatzResearch.WordTrace tailWord_1747490 prefixEnd_1747490 199400513094549593564099 := by
  unfold tailWord_1747490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15934049109787413094121981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42490797626099768250991949 15934049109787413094121981)
  ·
    refine ⟨5975268416170279910295743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15934049109787413094121981 5975268416170279910295743)
    ·
      refine ⟨8962902624255419865443615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975268416170279910295743 8962902624255419865443615)
      ·
        refine ⟨13444353936383129798165423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962902624255419865443615 13444353936383129798165423)
        ·
          refine ⟨20166530904574694697248135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444353936383129798165423 20166530904574694697248135)
          ·
            refine ⟨30249796356862042045872203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20166530904574694697248135 30249796356862042045872203)
            ·
              refine ⟨45374694535293063068808305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30249796356862042045872203 45374694535293063068808305)
              ·
                refine ⟨34031020901469797301606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45374694535293063068808305 34031020901469797301606229)
                ·
                  refine ⟨199400513094549593564099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34031020901469797301606229 199400513094549593564099)
                  ·
                    rfl

theorem cell22_1747490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1747490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747490 prefixEnd_1747490 := by exact prefixLift 1747490
  have htrace : WordTrace (prefixWord ++ tailWord_1747490) baseStart_1747490 baseEnd_1747490 := by
    simpa [prefixWord, tailWord_1747490, baseEnd_1747490] using wordTrace_append hprefix tailTrace_1747490
  have hstable : (prefixWord ++ tailWord_1747490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747490).length < 2 ^ (prefixWord ++ tailWord_1747490).sum := by decide
  have hdescent : baseEnd_1747490 < baseStart_1747490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747535 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 6]
def baseStart_1747535 : Nat := 118140960795 + 1747535 * 2 ^ 59
def prefixEnd_1747535 : Nat := 4983230072969 + 3 ^ 40 * 1747535 * 2
def baseEnd_1747535 : Nat := 199405647901094554439053

theorem tailTrace_1747535 : CollatzResearch.WordTrace tailWord_1747535 prefixEnd_1747535 199405647901094554439053 := by
  unfold tailWord_1747535
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737837723986625061876059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42491891815991083374584039 63737837723986625061876059)
  ·
    refine ⟨95606756585979937592814089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63737837723986625061876059 95606756585979937592814089)
    ·
      refine ⟨71705067439484953194610567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95606756585979937592814089 71705067439484953194610567)
      ·
        refine ⟨107557601159227429791915851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71705067439484953194610567 107557601159227429791915851)
        ·
          refine ⟨161336401738841144687873777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107557601159227429791915851 161336401738841144687873777)
          ·
            refine ⟨121002301304130858515905333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161336401738841144687873777 121002301304130858515905333)
            ·
              refine ⟨11343965747262267985866125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121002301304130858515905333 11343965747262267985866125)
              ·
                refine ⟨4253987155223350494699797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11343965747262267985866125 4253987155223350494699797)
                ·
                  refine ⟨199405647901094554439053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4253987155223350494699797 199405647901094554439053)
                  ·
                    rfl

theorem cell22_1747535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_1747535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747535 prefixEnd_1747535 := by exact prefixLift 1747535
  have htrace : WordTrace (prefixWord ++ tailWord_1747535) baseStart_1747535 baseEnd_1747535 := by
    simpa [prefixWord, tailWord_1747535, baseEnd_1747535] using wordTrace_append hprefix tailTrace_1747535
  have hstable : (prefixWord ++ tailWord_1747535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747535).length < 2 ^ (prefixWord ++ tailWord_1747535).sum := by decide
  have hdescent : baseEnd_1747535 < baseStart_1747535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747567 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 4, 3]
def baseStart_1747567 : Nat := 118140960795 + 1747567 * 2 ^ 59
def prefixEnd_1747567 : Nat := 4983230072969 + 3 ^ 40 * 1747567 * 2
def baseEnd_1747567 : Nat := 598227897957246246517061

theorem tailTrace_1747567 : CollatzResearch.WordTrace tailWord_1747567 prefixEnd_1747567 598227897957246246517061 := by
  unfold tailWord_1747567
  simp only [CollatzResearch.WordTrace]
  refine ⟨63739004859870694527040955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42492669906580463018027303 63739004859870694527040955)
  ·
    refine ⟨95608507289806041790561433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63739004859870694527040955 95608507289806041790561433)
    ·
      refine ⟨71706380467354531342921075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95608507289806041790561433 71706380467354531342921075)
      ·
        refine ⟨107559570701031797014381613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71706380467354531342921075 107559570701031797014381613)
        ·
          refine ⟨40334839012886923880393105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107559570701031797014381613 40334839012886923880393105)
          ·
            refine ⟨30251129259665192910294829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40334839012886923880393105 30251129259665192910294829)
            ·
              refine ⟨11344173472374447341360561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30251129259665192910294829 11344173472374447341360561)
              ·
                refine ⟨8508130104280835506020421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11344173472374447341360561 8508130104280835506020421)
                ·
                  refine ⟨1595274394552656657378829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8508130104280835506020421 1595274394552656657378829)
                  ·
                    refine ⟨598227897957246246517061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595274394552656657378829 598227897957246246517061)
                    ·
                      rfl

theorem cell22_1747567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_1747567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747567 prefixEnd_1747567 := by exact prefixLift 1747567
  have htrace : WordTrace (prefixWord ++ tailWord_1747567) baseStart_1747567 baseEnd_1747567 := by
    simpa [prefixWord, tailWord_1747567, baseEnd_1747567] using wordTrace_append hprefix tailTrace_1747567
  have hstable : (prefixWord ++ tailWord_1747567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747567).length < 2 ^ (prefixWord ++ tailWord_1747567).sum := by decide
  have hdescent : baseEnd_1747567 < baseStart_1747567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747580 : List Nat := [2, 2, 2, 1, 1, 2, 12]
def baseStart_1747580 : Nat := 118140960795 + 1747580 * 2 ^ 59
def prefixEnd_1747580 : Nat := 4983230072969 + 3 ^ 40 * 1747580 * 2
def baseEnd_1747580 : Nat := 22156753634182168368223

theorem tailTrace_1747580 : CollatzResearch.WordTrace tailWord_1747580 prefixEnd_1747580 22156753634182168368223 := by
  unfold tailWord_1747580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31869739504411798873632097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42492986005882398498176129 31869739504411798873632097)
  ·
    refine ⟨23902304628308849155224073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31869739504411798873632097 23902304628308849155224073)
    ·
      refine ⟨17926728471231636866418055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23902304628308849155224073 17926728471231636866418055)
      ·
        refine ⟨26890092706847455299627083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926728471231636866418055 26890092706847455299627083)
        ·
          refine ⟨40335139060271182949440625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26890092706847455299627083 40335139060271182949440625)
          ·
            refine ⟨30251354295203387212080469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40335139060271182949440625 30251354295203387212080469)
            ·
              refine ⟨22156753634182168368223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30251354295203387212080469 22156753634182168368223)
              ·
                rfl

theorem cell22_1747580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 12].length) (baseStart_1747580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747580 prefixEnd_1747580 := by exact prefixLift 1747580
  have htrace : WordTrace (prefixWord ++ tailWord_1747580) baseStart_1747580 baseEnd_1747580 := by
    simpa [prefixWord, tailWord_1747580, baseEnd_1747580] using wordTrace_append hprefix tailTrace_1747580
  have hstable : (prefixWord ++ tailWord_1747580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747580).length < 2 ^ (prefixWord ++ tailWord_1747580).sum := by decide
  have hdescent : baseEnd_1747580 < baseStart_1747580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747595 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_1747595 : Nat := 118140960795 + 1747595 * 2 ^ 59
def prefixEnd_1747595 : Nat := 4983230072969 + 3 ^ 40 * 1747595 * 2
def baseEnd_1747595 : Nat := 598237482929463506816975

theorem tailTrace_1747595 : CollatzResearch.WordTrace tailWord_1747595 prefixEnd_1747595 598237482929463506816975 := by
  unfold tailWord_1747595
  simp only [CollatzResearch.WordTrace]
  refine ⟨63740026103769255309060239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42493350735846170206040159 63740026103769255309060239)
  ·
    refine ⟨95610039155653882963590359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63740026103769255309060239 95610039155653882963590359)
    ·
      refine ⟨143415058733480824445385539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95610039155653882963590359 143415058733480824445385539)
      ·
        refine ⟨215122588100221236668078309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143415058733480824445385539 215122588100221236668078309)
        ·
          refine ⟨40335485268791481875264683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215122588100221236668078309 40335485268791481875264683)
          ·
            refine ⟨60503227903187222812897025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40335485268791481875264683 60503227903187222812897025)
            ·
              refine ⟨45377420927390417109672769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60503227903187222812897025 45377420927390417109672769)
              ·
                refine ⟨34033065695542812832254577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45377420927390417109672769 34033065695542812832254577)
                ·
                  refine ⟨25524799271657109624190933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34033065695542812832254577 25524799271657109624190933)
                  ·
                    refine ⟨598237482929463506816975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25524799271657109624190933 598237482929463506816975)
                    ·
                      rfl

theorem cell22_1747595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_1747595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747595 prefixEnd_1747595 := by exact prefixLift 1747595
  have htrace : WordTrace (prefixWord ++ tailWord_1747595) baseStart_1747595 baseEnd_1747595 := by
    simpa [prefixWord, tailWord_1747595, baseEnd_1747595] using wordTrace_append hprefix tailTrace_1747595
  have hstable : (prefixWord ++ tailWord_1747595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747595).length < 2 ^ (prefixWord ++ tailWord_1747595).sum := by decide
  have hdescent : baseEnd_1747595 < baseStart_1747595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747704 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_1747704 : Nat := 118140960795 + 1747704 * 2 ^ 59
def prefixEnd_1747704 : Nat := 4983230072969 + 3 ^ 40 * 1747704 * 2
def baseEnd_1747704 : Nat := 199424931952341185280547

theorem tailTrace_1747704 : CollatzResearch.WordTrace tailWord_1747704 prefixEnd_1747704 199424931952341185280547 := by
  unfold tailWord_1747704
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872000830187183462389083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42496001106916244616518777 31872000830187183462389083)
  ·
    refine ⟨47808001245280775193583625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31872000830187183462389083 47808001245280775193583625)
    ·
      refine ⟨35856000933960581395187719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47808001245280775193583625 35856000933960581395187719)
      ·
        refine ⟨53784001400940872092781579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35856000933960581395187719 53784001400940872092781579)
        ·
          refine ⟨80676002101411308139172369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53784001400940872092781579 80676002101411308139172369)
          ·
            refine ⟨60507001576058481104379277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80676002101411308139172369 60507001576058481104379277)
            ·
              refine ⟨22690125591021930414142229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60507001576058481104379277 22690125591021930414142229)
              ·
                refine ⟨1063599637079152988162917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22690125591021930414142229 1063599637079152988162917)
                ·
                  refine ⟨199424931952341185280547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063599637079152988162917 199424931952341185280547)
                  ·
                    rfl

theorem cell22_1747704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_1747704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747704 prefixEnd_1747704 := by exact prefixLift 1747704
  have htrace : WordTrace (prefixWord ++ tailWord_1747704) baseStart_1747704 baseEnd_1747704 := by
    simpa [prefixWord, tailWord_1747704, baseEnd_1747704] using wordTrace_append hprefix tailTrace_1747704
  have hstable : (prefixWord ++ tailWord_1747704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747704).length < 2 ^ (prefixWord ++ tailWord_1747704).sum := by decide
  have hdescent : baseEnd_1747704 < baseStart_1747704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747770 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_1747770 : Nat := 118140960795 + 1747770 * 2 ^ 59
def prefixEnd_1747770 : Nat := 4983230072969 + 3 ^ 40 * 1747770 * 2
def baseEnd_1747770 : Nat := 598297389005821383691439

theorem tailTrace_1747770 : CollatzResearch.WordTrace tailWord_1747770 prefixEnd_1747770 598297389005821383691439 := by
  unfold tailWord_1747770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936602219533815049170191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42497605918756840131120509 15936602219533815049170191)
  ·
    refine ⟨23904903329300722573755287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15936602219533815049170191 23904903329300722573755287)
    ·
      refine ⟨35857354993951083860632931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23904903329300722573755287 35857354993951083860632931)
      ·
        refine ⟨53786032490926625790949397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35857354993951083860632931 53786032490926625790949397)
        ·
          refine ⟨2521220273012185583950753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53786032490926625790949397 2521220273012185583950753)
          ·
            refine ⟨1890915204759139187963065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521220273012185583950753 1890915204759139187963065)
            ·
              refine ⟨1418186403569354390972299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890915204759139187963065 1418186403569354390972299)
              ·
                refine ⟨2127279605354031586458449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418186403569354390972299 2127279605354031586458449)
                ·
                  refine ⟨1595459704015523689843837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127279605354031586458449 1595459704015523689843837)
                  ·
                    refine ⟨598297389005821383691439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595459704015523689843837 598297389005821383691439)
                    ·
                      rfl

theorem cell22_1747770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_1747770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747770 prefixEnd_1747770 := by exact prefixLift 1747770
  have htrace : WordTrace (prefixWord ++ tailWord_1747770) baseStart_1747770 baseEnd_1747770 := by
    simpa [prefixWord, tailWord_1747770, baseEnd_1747770] using wordTrace_append hprefix tailTrace_1747770
  have hstable : (prefixWord ++ tailWord_1747770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747770).length < 2 ^ (prefixWord ++ tailWord_1747770).sum := by decide
  have hdescent : baseEnd_1747770 < baseStart_1747770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747811 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 5]
def baseStart_1747811 : Nat := 118140960795 + 1747811 * 2 ^ 59
def prefixEnd_1747811 : Nat := 4983230072969 + 3 ^ 40 * 1747811 * 2
def baseEnd_1747811 : Nat := 199437141381236981138771

theorem tailTrace_1747811 : CollatzResearch.WordTrace tailWord_1747811 prefixEnd_1747811 199437141381236981138771 := by
  unfold tailWord_1747811
  simp only [CollatzResearch.WordTrace]
  refine ⟨63747904270986724198923287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42498602847324482799282191 63747904270986724198923287)
  ·
    refine ⟨95621856406480086298384931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63747904270986724198923287 95621856406480086298384931)
    ·
      refine ⟨143432784609720129447577397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95621856406480086298384931 143432784609720129447577397)
      ·
        refine ⟨13446823557161262135710381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143432784609720129447577397 13446823557161262135710381)
        ·
          refine ⟨5042558833935473300891393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13446823557161262135710381 5042558833935473300891393)
          ·
            refine ⟨3781919125451604975668545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042558833935473300891393 3781919125451604975668545)
            ·
              refine ⟨2836439344088703731751409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3781919125451604975668545 2836439344088703731751409)
              ·
                refine ⟨2127329508066527798813557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836439344088703731751409 2127329508066527798813557)
                ·
                  refine ⟨199437141381236981138771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2127329508066527798813557 199437141381236981138771)
                  ·
                    rfl

theorem cell22_1747811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 5].length) (baseStart_1747811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747811 prefixEnd_1747811 := by exact prefixLift 1747811
  have htrace : WordTrace (prefixWord ++ tailWord_1747811) baseStart_1747811 baseEnd_1747811 := by
    simpa [prefixWord, tailWord_1747811, baseEnd_1747811] using wordTrace_append hprefix tailTrace_1747811
  have hstable : (prefixWord ++ tailWord_1747811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747811).length < 2 ^ (prefixWord ++ tailWord_1747811).sum := by decide
  have hdescent : baseEnd_1747811 < baseStart_1747811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747815 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1747815 : Nat := 118140960795 + 1747815 * 2 ^ 59
def prefixEnd_1747815 : Nat := 4983230072969 + 3 ^ 40 * 1747815 * 2
def baseEnd_1747815 : Nat := 598312793425456266316301

theorem tailTrace_1747815 : CollatzResearch.WordTrace tailWord_1747815 prefixEnd_1747815 598312793425456266316301 := by
  unfold tailWord_1747815
  simp only [CollatzResearch.WordTrace]
  refine ⟨63748050162972232882068899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42498700108648155254712599 63748050162972232882068899)
  ·
    refine ⟨95622075244458349323103349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63748050162972232882068899 95622075244458349323103349)
    ·
      refine ⟨8964569554167970249040939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95622075244458349323103349 8964569554167970249040939)
      ·
        refine ⟨13446854331251955373561409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964569554167970249040939 13446854331251955373561409)
        ·
          refine ⟨10085140748438966530171057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13446854331251955373561409 10085140748438966530171057)
          ·
            refine ⟨7563855561329224897628293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10085140748438966530171057 7563855561329224897628293)
            ·
              refine ⟨1418222917749229668305305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7563855561329224897628293 1418222917749229668305305)
              ·
                refine ⟨1063667188311922251228979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418222917749229668305305 1063667188311922251228979)
                ·
                  refine ⟨1595500782467883376843469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063667188311922251228979 1595500782467883376843469)
                  ·
                    refine ⟨598312793425456266316301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595500782467883376843469 598312793425456266316301)
                    ·
                      rfl

theorem cell22_1747815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1747815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747815 prefixEnd_1747815 := by exact prefixLift 1747815
  have htrace : WordTrace (prefixWord ++ tailWord_1747815) baseStart_1747815 baseEnd_1747815 := by
    simpa [prefixWord, tailWord_1747815, baseEnd_1747815] using wordTrace_append hprefix tailTrace_1747815
  have hstable : (prefixWord ++ tailWord_1747815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747815).length < 2 ^ (prefixWord ++ tailWord_1747815).sum := by decide
  have hdescent : baseEnd_1747815 < baseStart_1747815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747824 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_1747824 : Nat := 118140960795 + 1747824 * 2 ^ 59
def prefixEnd_1747824 : Nat := 4983230072969 + 3 ^ 40 * 1747824 * 2
def baseEnd_1747824 : Nat := 598315874309383242841273

theorem tailTrace_1747824 : CollatzResearch.WordTrace tailWord_1747824 prefixEnd_1747824 598315874309383242841273 := by
  unfold tailWord_1747824
  simp only [CollatzResearch.WordTrace]
  refine ⟨31874189209969813709573263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42498918946626418279431017 31874189209969813709573263)
  ·
    refine ⟨47811283814954720564359895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31874189209969813709573263 47811283814954720564359895)
    ·
      refine ⟨71716925722432080846539843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47811283814954720564359895 71716925722432080846539843)
      ·
        refine ⟨107575388583648121269809765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71716925722432080846539843 107575388583648121269809765)
        ·
          refine ⟨20170385359434022738089331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107575388583648121269809765 20170385359434022738089331)
          ·
            refine ⟨30255578039151034107133997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20170385359434022738089331 30255578039151034107133997)
            ·
              refine ⟨11345841764681637790175249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30255578039151034107133997 11345841764681637790175249)
              ·
                refine ⟨8509381323511228342631437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11345841764681637790175249 8509381323511228342631437)
                ·
                  refine ⟨3191017996316710628486789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8509381323511228342631437 3191017996316710628486789)
                  ·
                    refine ⟨598315874309383242841273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191017996316710628486789 598315874309383242841273)
                    ·
                      rfl

theorem cell22_1747824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_1747824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747824 prefixEnd_1747824 := by exact prefixLift 1747824
  have htrace : WordTrace (prefixWord ++ tailWord_1747824) baseStart_1747824 baseEnd_1747824 := by
    simpa [prefixWord, tailWord_1747824, baseEnd_1747824] using wordTrace_append hprefix tailTrace_1747824
  have hstable : (prefixWord ++ tailWord_1747824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747824).length < 2 ^ (prefixWord ++ tailWord_1747824).sum := by decide
  have hdescent : baseEnd_1747824 < baseStart_1747824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747862 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1747862 : Nat := 118140960795 + 1747862 * 2 ^ 59
def prefixEnd_1747862 : Nat := 4983230072969 + 3 ^ 40 * 1747862 * 2
def baseEnd_1747862 : Nat := 199442960828654603463719

theorem tailTrace_1747862 : CollatzResearch.WordTrace tailWord_1747862 prefixEnd_1747862 199442960828654603463719 := by
  unfold tailWord_1747862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984360274612622494314365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42499842929201306606019893 3984360274612622494314365)
  ·
    refine ⟨1494135102979733435367887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3984360274612622494314365 1494135102979733435367887)
    ·
      refine ⟨2241202654469600153051831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494135102979733435367887 2241202654469600153051831)
      ·
        refine ⟨3361803981704400229577747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241202654469600153051831 3361803981704400229577747)
        ·
          refine ⟨5042705972556600344366621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361803981704400229577747 5042705972556600344366621)
          ·
            refine ⟨1891014739708725129137483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5042705972556600344366621 1891014739708725129137483)
            ·
              refine ⟨2836522109563087693706225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891014739708725129137483 2836522109563087693706225)
              ·
                refine ⟨2127391582172315770279669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836522109563087693706225 2127391582172315770279669)
                ·
                  refine ⟨199442960828654603463719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2127391582172315770279669 199442960828654603463719)
                  ·
                    rfl

theorem cell22_1747862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1747862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747862 prefixEnd_1747862 := by exact prefixLift 1747862
  have htrace : WordTrace (prefixWord ++ tailWord_1747862) baseStart_1747862 baseEnd_1747862 := by
    simpa [prefixWord, tailWord_1747862, baseEnd_1747862] using wordTrace_append hprefix tailTrace_1747862
  have hstable : (prefixWord ++ tailWord_1747862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747862).length < 2 ^ (prefixWord ++ tailWord_1747862).sum := by decide
  have hdescent : baseEnd_1747862 < baseStart_1747862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747873 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 4]
def baseStart_1747873 : Nat := 118140960795 + 1747873 * 2 ^ 59
def prefixEnd_1747873 : Nat := 4983230072969 + 3 ^ 40 * 1747873 * 2
def baseEnd_1747873 : Nat := 199444216003587816122041

theorem tailTrace_1747873 : CollatzResearch.WordTrace tailWord_1747873 prefixEnd_1747873 199444216003587816122041 := by
  unfold tailWord_1747873
  simp only [CollatzResearch.WordTrace]
  refine ⟨63750165596762108787680273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42500110397841405858453515 63750165596762108787680273)
  ·
    refine ⟨47812624197571581590760205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63750165596762108787680273 47812624197571581590760205)
    ·
      refine ⟨17929734074089343096535077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47812624197571581590760205 17929734074089343096535077)
      ·
        refine ⟨3361825138891751830600327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17929734074089343096535077 3361825138891751830600327)
        ·
          refine ⟨5042737708337627745900491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361825138891751830600327 5042737708337627745900491)
          ·
            refine ⟨7564106562506441618850737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042737708337627745900491 7564106562506441618850737)
            ·
              refine ⟨5673079921879831214138053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7564106562506441618850737 5673079921879831214138053)
              ·
                refine ⟨1063702485352468352650885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5673079921879831214138053 1063702485352468352650885)
                ·
                  refine ⟨199444216003587816122041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063702485352468352650885 199444216003587816122041)
                  ·
                    rfl

theorem cell22_1747873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_1747873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747873 prefixEnd_1747873 := by exact prefixLift 1747873
  have htrace : WordTrace (prefixWord ++ tailWord_1747873) baseStart_1747873 baseEnd_1747873 := by
    simpa [prefixWord, tailWord_1747873, baseEnd_1747873] using wordTrace_append hprefix tailTrace_1747873
  have hstable : (prefixWord ++ tailWord_1747873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747873).length < 2 ^ (prefixWord ++ tailWord_1747873).sum := by decide
  have hdescent : baseEnd_1747873 < baseStart_1747873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747901 : List Nat := [1, 4, 1, 2, 4, 1, 1, 8]
def baseStart_1747901 : Nat := 118140960795 + 1747901 * 2 ^ 59
def prefixEnd_1747901 : Nat := 4983230072969 + 3 ^ 40 * 1747901 * 2
def baseEnd_1747901 : Nat := 66482470331442300962893

theorem tailTrace_1747901 : CollatzResearch.WordTrace tailWord_1747901 prefixEnd_1747901 66482470331442300962893 := by
  unfold tailWord_1747901
  simp only [CollatzResearch.WordTrace]
  refine ⟨63751186840660669569699557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42500791227107113046466371 63751186840660669569699557)
  ·
    refine ⟨11953347532623875544318667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63751186840660669569699557 11953347532623875544318667)
    ·
      refine ⟨17930021298935813316478001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11953347532623875544318667 17930021298935813316478001)
      ·
        refine ⟨13447515974201859987358501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17930021298935813316478001 13447515974201859987358501)
        ·
          refine ⟨2521409245162848747629719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13447515974201859987358501 2521409245162848747629719)
          ·
            refine ⟨3782113867744273121444579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521409245162848747629719 3782113867744273121444579)
            ·
              refine ⟨5673170801616409682166869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782113867744273121444579 5673170801616409682166869)
              ·
                refine ⟨66482470331442300962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5673170801616409682166869 66482470331442300962893)
                ·
                  rfl

theorem cell22_1747901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 8].length) (baseStart_1747901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747901 prefixEnd_1747901 := by exact prefixLift 1747901
  have htrace : WordTrace (prefixWord ++ tailWord_1747901) baseStart_1747901 baseEnd_1747901 := by
    simpa [prefixWord, tailWord_1747901, baseEnd_1747901] using wordTrace_append hprefix tailTrace_1747901
  have hstable : (prefixWord ++ tailWord_1747901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747901).length < 2 ^ (prefixWord ++ tailWord_1747901).sum := by decide
  have hdescent : baseEnd_1747901 < baseStart_1747901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747914 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1747914 : Nat := 118140960795 + 1747914 * 2 ^ 59
def prefixEnd_1747914 : Nat := 4983230072969 + 3 ^ 40 * 1747914 * 2
def baseEnd_1747914 : Nat := 598346683148653008090997

theorem tailTrace_1747914 : CollatzResearch.WordTrace tailWord_1747914 prefixEnd_1747914 598346683148653008090997 := by
  unfold tailWord_1747914
  simp only [CollatzResearch.WordTrace]
  refine ⟨15937915247403393197480699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42501107326409048526615197 15937915247403393197480699)
  ·
    refine ⟨23906872871105089796221049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15937915247403393197480699 23906872871105089796221049)
    ·
      refine ⟨17930154653328817347165787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23906872871105089796221049 17930154653328817347165787)
      ·
        refine ⟨26895231979993226020748681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930154653328817347165787 26895231979993226020748681)
        ·
          refine ⟨20171423984994919515561511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26895231979993226020748681 20171423984994919515561511)
          ·
            refine ⟨30257135977492379273342267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20171423984994919515561511 30257135977492379273342267)
            ·
              refine ⟨45385703966238568910013401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30257135977492379273342267 45385703966238568910013401)
              ·
                refine ⟨34039277974678926682510051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45385703966238568910013401 34039277974678926682510051)
                ·
                  refine ⟨51058916962018390023765077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34039277974678926682510051 51058916962018390023765077)
                  ·
                    refine ⟨598346683148653008090997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51058916962018390023765077 598346683148653008090997)
                    ·
                      rfl

theorem cell22_1747914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1747914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1747914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1747914 prefixEnd_1747914 := by exact prefixLift 1747914
  have htrace : WordTrace (prefixWord ++ tailWord_1747914) baseStart_1747914 baseEnd_1747914 := by
    simpa [prefixWord, tailWord_1747914, baseEnd_1747914] using wordTrace_append hprefix tailTrace_1747914
  have hstable : (prefixWord ++ tailWord_1747914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747914).length < 2 ^ (prefixWord ++ tailWord_1747914).sum := by decide
  have hdescent : baseEnd_1747914 < baseStart_1747914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748025 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 4]
def baseStart_1748025 : Nat := 118140960795 + 1748025 * 2 ^ 59
def prefixEnd_1748025 : Nat := 4983230072969 + 3 ^ 40 * 1748025 * 2
def baseEnd_1748025 : Nat := 199461560239028572855219

theorem tailTrace_1748025 : CollatzResearch.WordTrace tailWord_1748025 prefixEnd_1748025 199461560239028572855219 := by
  unfold tailWord_1748025
  simp only [CollatzResearch.WordTrace]
  refine ⟨63755709492211438747213529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42503806328140959164809019 63755709492211438747213529)
  ·
    refine ⟨47816782119158579060410147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63755709492211438747213529 47816782119158579060410147)
    ·
      refine ⟨71725173178737868590615221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47816782119158579060410147 71725173178737868590615221)
      ·
        refine ⟨6724234985506675180370177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71725173178737868590615221 6724234985506675180370177)
        ·
          refine ⟨5043176239130006385277633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724234985506675180370177 5043176239130006385277633)
          ·
            refine ⟨3782382179347504788958225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043176239130006385277633 3782382179347504788958225)
            ·
              refine ⟨2836786634510628591718669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3782382179347504788958225 2836786634510628591718669)
              ·
                refine ⟨1063794987941485721894501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2836786634510628591718669 1063794987941485721894501)
                ·
                  refine ⟨199461560239028572855219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063794987941485721894501 199461560239028572855219)
                  ·
                    rfl

theorem cell22_1748025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_1748025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748025 prefixEnd_1748025 := by exact prefixLift 1748025
  have htrace : WordTrace (prefixWord ++ tailWord_1748025) baseStart_1748025 baseEnd_1748025 := by
    simpa [prefixWord, tailWord_1748025, baseEnd_1748025] using wordTrace_append hprefix tailTrace_1748025
  have hstable : (prefixWord ++ tailWord_1748025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748025).length < 2 ^ (prefixWord ++ tailWord_1748025).sum := by decide
  have hdescent : baseEnd_1748025 < baseStart_1748025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748096 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_1748096 : Nat := 118140960795 + 1748096 * 2 ^ 59
def prefixEnd_1748096 : Nat := 4983230072969 + 3 ^ 40 * 1748096 * 2
def baseEnd_1748096 : Nat := 598408985468065200040439

theorem tailTrace_1748096 : CollatzResearch.WordTrace tailWord_1748096 prefixEnd_1748096 598408985468065200040439 := by
  unfold tailWord_1748096
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879149537477108936524071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42505532716636145248698761 31879149537477108936524071)
  ·
    refine ⟨47818724306215663404786107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31879149537477108936524071 47818724306215663404786107)
    ·
      refine ⟨71728086459323495107179161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47818724306215663404786107 71728086459323495107179161)
      ·
        refine ⟨53796064844492621330384371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71728086459323495107179161 53796064844492621330384371)
        ·
          refine ⟨80694097266738931995576557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53796064844492621330384371 80694097266738931995576557)
          ·
            refine ⟨30260286475027099498341209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80694097266738931995576557 30260286475027099498341209)
            ·
              refine ⟨22695214856270324623755907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30260286475027099498341209 22695214856270324623755907)
              ·
                refine ⟨34042822284405486935633861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22695214856270324623755907 34042822284405486935633861)
                ·
                  refine ⟨6383029178326028800431349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34042822284405486935633861 6383029178326028800431349)
                  ·
                    refine ⟨598408985468065200040439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6383029178326028800431349 598408985468065200040439)
                    ·
                      rfl

theorem cell22_1748096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_1748096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748096 prefixEnd_1748096 := by exact prefixLift 1748096
  have htrace : WordTrace (prefixWord ++ tailWord_1748096) baseStart_1748096 baseEnd_1748096 := by
    simpa [prefixWord, tailWord_1748096, baseEnd_1748096] using wordTrace_append hprefix tailTrace_1748096
  have hstable : (prefixWord ++ tailWord_1748096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748096).length < 2 ^ (prefixWord ++ tailWord_1748096).sum := by decide
  have hdescent : baseEnd_1748096 < baseStart_1748096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748128 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_1748128 : Nat := 118140960795 + 1748128 * 2 ^ 59
def prefixEnd_1748128 : Nat := 4983230072969 + 3 ^ 40 * 1748128 * 2
def baseEnd_1748128 : Nat := 598419939722027783240341

theorem tailTrace_1748128 : CollatzResearch.WordTrace tailWord_1748128 prefixEnd_1748128 598419939722027783240341 := by
  unfold tailWord_1748128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879733105419143669106519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42506310807225524892142025 31879733105419143669106519)
  ·
    refine ⟨47819599658128715503659779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31879733105419143669106519 47819599658128715503659779)
    ·
      refine ⟨71729399487193073255489669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47819599658128715503659779 71729399487193073255489669)
      ·
        refine ⟨13449262403848701235404313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71729399487193073255489669 13449262403848701235404313)
        ·
          refine ⟨10086946802886525926553235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13449262403848701235404313 10086946802886525926553235)
          ·
            refine ⟨15130420204329788889829853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086946802886525926553235 15130420204329788889829853)
            ·
              refine ⟨5673907576623670833686195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15130420204329788889829853 5673907576623670833686195)
              ·
                refine ⟨8510861364935506250529293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673907576623670833686195 8510861364935506250529293)
                ·
                  refine ⟨3191573011850814843948485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8510861364935506250529293 3191573011850814843948485)
                  ·
                    refine ⟨598419939722027783240341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191573011850814843948485 598419939722027783240341)
                    ·
                      rfl

theorem cell22_1748128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_1748128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748128 prefixEnd_1748128 := by exact prefixLift 1748128
  have htrace : WordTrace (prefixWord ++ tailWord_1748128) baseStart_1748128 baseEnd_1748128 := by
    simpa [prefixWord, tailWord_1748128, baseEnd_1748128] using wordTrace_append hprefix tailTrace_1748128
  have hstable : (prefixWord ++ tailWord_1748128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748128).length < 2 ^ (prefixWord ++ tailWord_1748128).sum := by decide
  have hdescent : baseEnd_1748128 < baseStart_1748128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748171 : List Nat := [1, 1, 1, 1, 3, 2, 2, 11]
def baseStart_1748171 : Nat := 118140960795 + 1748171 * 2 ^ 59
def prefixEnd_1748171 : Nat := 4983230072969 + 3 ^ 40 * 1748171 * 2
def baseEnd_1748171 : Nat := 66492739944532222712801

theorem tailTrace_1748171 : CollatzResearch.WordTrace tailWord_1748171 prefixEnd_1748171 66492739944532222712801 := by
  unfold tailWord_1748171
  simp only [CollatzResearch.WordTrace]
  refine ⟨63761034549682505682028367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42507356366455003788018911 63761034549682505682028367)
  ·
    refine ⟨95641551824523758523042551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63761034549682505682028367 95641551824523758523042551)
    ·
      refine ⟨143462327736785637784563827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95641551824523758523042551 143462327736785637784563827)
      ·
        refine ⟨215193491605178456676845741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143462327736785637784563827 215193491605178456676845741)
        ·
          refine ⟨80697559351941921253817153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215193491605178456676845741 80697559351941921253817153)
          ·
            refine ⟨60523169513956440940362865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80697559351941921253817153 60523169513956440940362865)
            ·
              refine ⟨45392377135467330705272149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60523169513956440940362865 45392377135467330705272149)
              ·
                refine ⟨66492739944532222712801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 45392377135467330705272149 66492739944532222712801)
                ·
                  rfl

theorem cell22_1748171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 11].length) (baseStart_1748171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748171 prefixEnd_1748171 := by exact prefixLift 1748171
  have htrace : WordTrace (prefixWord ++ tailWord_1748171) baseStart_1748171 baseEnd_1748171 := by
    simpa [prefixWord, tailWord_1748171, baseEnd_1748171] using wordTrace_append hprefix tailTrace_1748171
  have hstable : (prefixWord ++ tailWord_1748171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748171).length < 2 ^ (prefixWord ++ tailWord_1748171).sum := by decide
  have hdescent : baseEnd_1748171 < baseStart_1748171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748226 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1748226 : Nat := 118140960795 + 1748226 * 2 ^ 59
def prefixEnd_1748226 : Nat := 4983230072969 + 3 ^ 40 * 1748226 * 2
def baseEnd_1748226 : Nat := 598453487124788194290041

theorem tailTrace_1748226 : CollatzResearch.WordTrace tailWord_1748226 prefixEnd_1748226 598453487124788194290041 := by
  unfold tailWord_1748226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15940760141120812518820133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42508693709655500050187021 15940760141120812518820133)
  ·
    refine ⟨2988892526460152347278775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15940760141120812518820133 2988892526460152347278775)
    ·
      refine ⟨4483338789690228520918163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988892526460152347278775 4483338789690228520918163)
      ·
        refine ⟨6725008184535342781377245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483338789690228520918163 6725008184535342781377245)
        ·
          refine ⟨2521878069200753543016467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6725008184535342781377245 2521878069200753543016467)
          ·
            refine ⟨3782817103801130314524701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521878069200753543016467 3782817103801130314524701)
            ·
              refine ⟨1418556413925423867946763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3782817103801130314524701 1418556413925423867946763)
              ·
                refine ⟨2127834620888135801920145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418556413925423867946763 2127834620888135801920145)
                ·
                  refine ⟨1595875965666101851440109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127834620888135801920145 1595875965666101851440109)
                  ·
                    refine ⟨598453487124788194290041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1595875965666101851440109 598453487124788194290041)
                    ·
                      rfl

theorem cell22_1748226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1748226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748226 prefixEnd_1748226 := by exact prefixLift 1748226
  have htrace : WordTrace (prefixWord ++ tailWord_1748226) baseStart_1748226 baseEnd_1748226 := by
    simpa [prefixWord, tailWord_1748226, baseEnd_1748226] using wordTrace_append hprefix tailTrace_1748226
  have hstable : (prefixWord ++ tailWord_1748226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748226).length < 2 ^ (prefixWord ++ tailWord_1748226).sum := by decide
  have hdescent : baseEnd_1748226 < baseStart_1748226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748293 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1748293 : Nat := 118140960795 + 1748293 * 2 ^ 59
def prefixEnd_1748293 : Nat := 4983230072969 + 3 ^ 40 * 1748293 * 2
def baseEnd_1748293 : Nat := 598476422594022352864835

theorem tailTrace_1748293 : CollatzResearch.WordTrace tailWord_1748293 prefixEnd_1748293 598476422594022352864835 := by
  unfold tailWord_1748293
  simp only [CollatzResearch.WordTrace]
  refine ⟨63765484255240520517969533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42510322836827013678646355 63765484255240520517969533)
  ·
    refine ⟨23912056595715195194238575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63765484255240520517969533 23912056595715195194238575)
    ·
      refine ⟨35868084893572792791357863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23912056595715195194238575 35868084893572792791357863)
      ·
        refine ⟨53802127340359189187036795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35868084893572792791357863 53802127340359189187036795)
        ·
          refine ⟨80703191010538783780555193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53802127340359189187036795 80703191010538783780555193)
          ·
            refine ⟨60527393257904087835416395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80703191010538783780555193 60527393257904087835416395)
            ·
              refine ⟨90791089886856131753124593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60527393257904087835416395 90791089886856131753124593)
              ·
                refine ⟨68093317415142098814843445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90791089886856131753124593 68093317415142098814843445)
                ·
                  refine ⟨6383748507669571763891573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68093317415142098814843445 6383748507669571763891573)
                  ·
                    refine ⟨598476422594022352864835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6383748507669571763891573 598476422594022352864835)
                    ·
                      rfl

theorem cell22_1748293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1748293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748293 prefixEnd_1748293 := by exact prefixLift 1748293
  have htrace : WordTrace (prefixWord ++ tailWord_1748293) baseStart_1748293 baseEnd_1748293 := by
    simpa [prefixWord, tailWord_1748293, baseEnd_1748293] using wordTrace_append hprefix tailTrace_1748293
  have hstable : (prefixWord ++ tailWord_1748293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748293).length < 2 ^ (prefixWord ++ tailWord_1748293).sum := by decide
  have hdescent : baseEnd_1748293 < baseStart_1748293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748323 : List Nat := [1, 1, 1, 5, 2, 12]
def baseStart_1748323 : Nat := 118140960795 + 1748323 * 2 ^ 59
def prefixEnd_1748323 : Nat := 4983230072969 + 3 ^ 40 * 1748323 * 2
def baseEnd_1748323 : Nat := 7388724595149534254503

theorem tailTrace_1748323 : CollatzResearch.WordTrace tailWord_1748323 prefixEnd_1748323 7388724595149534254503 := by
  unfold tailWord_1748323
  simp only [CollatzResearch.WordTrace]
  refine ⟨63766578445131835641561623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42511052296754557094374415 63766578445131835641561623)
  ·
    refine ⟨95649867667697753462342435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63766578445131835641561623 95649867667697753462342435)
    ·
      refine ⟨143474801501546630193513653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95649867667697753462342435 143474801501546630193513653)
      ·
        refine ⟨13450762640769996580641905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143474801501546630193513653 13450762640769996580641905)
        ·
          refine ⟨10088071980577497435481429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13450762640769996580641905 10088071980577497435481429)
          ·
            refine ⟨7388724595149534254503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10088071980577497435481429 7388724595149534254503)
            ·
              rfl

theorem cell22_1748323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 12].length) (baseStart_1748323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748323 prefixEnd_1748323 := by exact prefixLift 1748323
  have htrace : WordTrace (prefixWord ++ tailWord_1748323) baseStart_1748323 baseEnd_1748323 := by
    simpa [prefixWord, tailWord_1748323, baseEnd_1748323] using wordTrace_append hprefix tailTrace_1748323
  have hstable : (prefixWord ++ tailWord_1748323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748323).length < 2 ^ (prefixWord ++ tailWord_1748323).sum := by decide
  have hdescent : baseEnd_1748323 < baseStart_1748323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748325 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_1748325 : Nat := 118140960795 + 1748325 * 2 ^ 59
def prefixEnd_1748325 : Nat := 4983230072969 + 3 ^ 40 * 1748325 * 2
def baseEnd_1748325 : Nat := 598487376847984936064737

theorem tailTrace_1748325 : CollatzResearch.WordTrace tailWord_1748325 prefixEnd_1748325 598487376847984936064737 := by
  unfold tailWord_1748325
  simp only [CollatzResearch.WordTrace]
  refine ⟨63766651391124589983134429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42511100927416393322089619 63766651391124589983134429)
  ·
    refine ⟨23912494271671721243675411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63766651391124589983134429 23912494271671721243675411)
    ·
      refine ⟨35868741407507581865513117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23912494271671721243675411 35868741407507581865513117)
      ·
        refine ⟨13450778027815343199567419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35868741407507581865513117 13450778027815343199567419)
        ·
          refine ⟨20176167041723014799351129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450778027815343199567419 20176167041723014799351129)
          ·
            refine ⟨15132125281292261099513347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20176167041723014799351129 15132125281292261099513347)
            ·
              refine ⟨22698187921938391649270021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15132125281292261099513347 22698187921938391649270021)
              ·
                refine ⟨4255910235363448434238129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22698187921938391649270021 4255910235363448434238129)
                ·
                  refine ⟨3191932676522586325678597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255910235363448434238129 3191932676522586325678597)
                  ·
                    refine ⟨598487376847984936064737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191932676522586325678597 598487376847984936064737)
                    ·
                      rfl

theorem cell22_1748325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_1748325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748325 prefixEnd_1748325 := by exact prefixLift 1748325
  have htrace : WordTrace (prefixWord ++ tailWord_1748325) baseStart_1748325 baseEnd_1748325 := by
    simpa [prefixWord, tailWord_1748325, baseEnd_1748325] using wordTrace_append hprefix tailTrace_1748325
  have hstable : (prefixWord ++ tailWord_1748325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748325).length < 2 ^ (prefixWord ++ tailWord_1748325).sum := by decide
  have hdescent : baseEnd_1748325 < baseStart_1748325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748415 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_1748415 : Nat := 118140960795 + 1748415 * 2 ^ 59
def prefixEnd_1748415 : Nat := 4983230072969 + 3 ^ 40 * 1748415 * 2
def baseEnd_1748415 : Nat := 598518185687254701314461

theorem tailTrace_1748415 : CollatzResearch.WordTrace tailWord_1748415 prefixEnd_1748415 598518185687254701314461 := by
  unfold tailWord_1748415
  simp only [CollatzResearch.WordTrace]
  refine ⟨63769933960798535353910699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42513289307199023569273799 63769933960798535353910699)
  ·
    refine ⟨95654900941197803030866049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63769933960798535353910699 95654900941197803030866049)
    ·
      refine ⟨71741175705898352273149537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95654900941197803030866049 71741175705898352273149537)
      ·
        refine ⟨53805881779423764204862153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71741175705898352273149537 53805881779423764204862153)
        ·
          refine ⟨40354411334567823153646615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53805881779423764204862153 40354411334567823153646615)
          ·
            refine ⟨60531617001851734730469923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40354411334567823153646615 60531617001851734730469923)
            ·
              refine ⟨90797425502777602095704885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60531617001851734730469923 90797425502777602095704885)
              ·
                refine ⟨8512258640885400196472333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90797425502777602095704885 8512258640885400196472333)
                ·
                  refine ⟨3192096990332025073677125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8512258640885400196472333 3192096990332025073677125)
                  ·
                    refine ⟨598518185687254701314461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192096990332025073677125 598518185687254701314461)
                    ·
                      rfl

theorem cell22_1748415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_1748415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748415 prefixEnd_1748415 := by exact prefixLift 1748415
  have htrace : WordTrace (prefixWord ++ tailWord_1748415) baseStart_1748415 baseEnd_1748415 := by
    simpa [prefixWord, tailWord_1748415, baseEnd_1748415] using wordTrace_append hprefix tailTrace_1748415
  have hstable : (prefixWord ++ tailWord_1748415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748415).length < 2 ^ (prefixWord ++ tailWord_1748415).sum := by decide
  have hdescent : baseEnd_1748415 < baseStart_1748415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748430 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1748430 : Nat := 118140960795 + 1748430 * 2 ^ 59
def prefixEnd_1748430 : Nat := 4983230072969 + 3 ^ 40 * 1748430 * 2
def baseEnd_1748430 : Nat := 199507773497933220729805

theorem tailTrace_1748430 : CollatzResearch.WordTrace tailWord_1748430 prefixEnd_1748430 199507773497933220729805 := by
  unfold tailWord_1748430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971310131968024114463343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42513654037162795277137829 7971310131968024114463343)
  ·
    refine ⟨11956965197952036171695015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7971310131968024114463343 11956965197952036171695015)
    ·
      refine ⟨17935447796928054257542523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11956965197952036171695015 17935447796928054257542523)
      ·
        refine ⟨26903171695392081386313785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17935447796928054257542523 26903171695392081386313785)
        ·
          refine ⟨20177378771544061039735339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26903171695392081386313785 20177378771544061039735339)
          ·
            refine ⟨30266068157316091559603009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177378771544061039735339 30266068157316091559603009)
            ·
              refine ⟨22699551117987068669702257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30266068157316091559603009 22699551117987068669702257)
              ·
                refine ⟨17024663338490301502276693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22699551117987068669702257 17024663338490301502276693)
                ·
                  refine ⟨199507773497933220729805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17024663338490301502276693 199507773497933220729805)
                  ·
                    rfl

theorem cell22_1748430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1748430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748430 prefixEnd_1748430 := by exact prefixLift 1748430
  have htrace : WordTrace (prefixWord ++ tailWord_1748430) baseStart_1748430 baseEnd_1748430 := by
    simpa [prefixWord, tailWord_1748430, baseEnd_1748430] using wordTrace_append hprefix tailTrace_1748430
  have hstable : (prefixWord ++ tailWord_1748430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748430).length < 2 ^ (prefixWord ++ tailWord_1748430).sum := by decide
  have hdescent : baseEnd_1748430 < baseStart_1748430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748460 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1748460 : Nat := 118140960795 + 1748460 * 2 ^ 59
def prefixEnd_1748460 : Nat := 4983230072969 + 3 ^ 40 * 1748460 * 2
def baseEnd_1748460 : Nat := 598533590106889583939323

theorem tailTrace_1748460 : CollatzResearch.WordTrace tailWord_1748460 prefixEnd_1748460 598533590106889583939323 := by
  unfold tailWord_1748460
  simp only [CollatzResearch.WordTrace]
  refine ⟨31885787622817754019649417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42514383497090338692865889 31885787622817754019649417)
  ·
    refine ⟨23914340717113315514737063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31885787622817754019649417 23914340717113315514737063)
    ·
      refine ⟨35871511075669973272105595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23914340717113315514737063 35871511075669973272105595)
      ·
        refine ⟨53807266613504959908158393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35871511075669973272105595 53807266613504959908158393)
        ·
          refine ⟨40355449960128719931118795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53807266613504959908158393 40355449960128719931118795)
          ·
            refine ⟨60533174940193079896678193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40355449960128719931118795 60533174940193079896678193)
            ·
              refine ⟨45399881205144809922508645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60533174940193079896678193 45399881205144809922508645)
              ·
                refine ⟨8512477725964651860470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45399881205144809922508645 8512477725964651860470371)
                ·
                  refine ⟨12768716588946977790705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8512477725964651860470371 12768716588946977790705557)
                  ·
                    refine ⟨598533590106889583939323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12768716588946977790705557 598533590106889583939323)
                    ·
                      rfl

theorem cell22_1748460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1748460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748460 prefixEnd_1748460 := by exact prefixLift 1748460
  have htrace : WordTrace (prefixWord ++ tailWord_1748460) baseStart_1748460 baseEnd_1748460 := by
    simpa [prefixWord, tailWord_1748460, baseEnd_1748460] using wordTrace_append hprefix tailTrace_1748460
  have hstable : (prefixWord ++ tailWord_1748460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748460).length < 2 ^ (prefixWord ++ tailWord_1748460).sum := by decide
  have hdescent : baseEnd_1748460 < baseStart_1748460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748462 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1748462 : Nat := 118140960795 + 1748462 * 2 ^ 59
def prefixEnd_1748462 : Nat := 4983230072969 + 3 ^ 40 * 1748462 * 2
def baseEnd_1748462 : Nat := 598534274747762245389317

theorem tailTrace_1748462 : CollatzResearch.WordTrace tailWord_1748462 prefixEnd_1748462 598534274747762245389317 := by
  unfold tailWord_1748462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971456023953532797608955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42514432127752174920581093 7971456023953532797608955)
  ·
    refine ⟨11957184035930299196413433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7971456023953532797608955 11957184035930299196413433)
    ·
      refine ⟨8967888026947724397310075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11957184035930299196413433 8967888026947724397310075)
      ·
        refine ⟨13451832040421586595965113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8967888026947724397310075 13451832040421586595965113)
        ·
          refine ⟨10088874030316189946973835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13451832040421586595965113 10088874030316189946973835)
          ·
            refine ⟨15133311045474284920460753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10088874030316189946973835 15133311045474284920460753)
            ·
              refine ⟨11349983284105713690345565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15133311045474284920460753 11349983284105713690345565)
              ·
                refine ⟨4256243731539642633879587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11349983284105713690345565 4256243731539642633879587)
                ·
                  refine ⟨6384365597309463950819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256243731539642633879587 6384365597309463950819381)
                  ·
                    refine ⟨598534274747762245389317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6384365597309463950819381 598534274747762245389317)
                    ·
                      rfl

theorem cell22_1748462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1748462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748462 prefixEnd_1748462 := by exact prefixLift 1748462
  have htrace : WordTrace (prefixWord ++ tailWord_1748462) baseStart_1748462 baseEnd_1748462 := by
    simpa [prefixWord, tailWord_1748462, baseEnd_1748462] using wordTrace_append hprefix tailTrace_1748462
  have hstable : (prefixWord ++ tailWord_1748462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748462).length < 2 ^ (prefixWord ++ tailWord_1748462).sum := by decide
  have hdescent : baseEnd_1748462 < baseStart_1748462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748466 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1748466 : Nat := 118140960795 + 1748466 * 2 ^ 59
def prefixEnd_1748466 : Nat := 4983230072969 + 3 ^ 40 * 1748466 * 2
def baseEnd_1748466 : Nat := 598535644029507568289305

theorem tailTrace_1748466 : CollatzResearch.WordTrace tailWord_1748466 prefixEnd_1748466 598535644029507568289305 := by
  unfold tailWord_1748466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942948520903442766004313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42514529389075847376011501 15942948520903442766004313)
  ·
    refine ⟨11957211390677582074503235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15942948520903442766004313 11957211390677582074503235)
    ·
      refine ⟨17935817086016373111754853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11957211390677582074503235 17935817086016373111754853)
      ·
        refine ⟨3362965703628069958454035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17935817086016373111754853 3362965703628069958454035)
        ·
          refine ⟨5044448555442104937681053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362965703628069958454035 5044448555442104937681053)
          ·
            refine ⟨1891668208290789351630395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5044448555442104937681053 1891668208290789351630395)
            ·
              refine ⟨2837502312436184027445593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891668208290789351630395 2837502312436184027445593)
              ·
                refine ⟨2128126734327138020584195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837502312436184027445593 2128126734327138020584195)
                ·
                  refine ⟨3192190101490707030876293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128126734327138020584195 3192190101490707030876293)
                  ·
                    refine ⟨598535644029507568289305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192190101490707030876293 598535644029507568289305)
                    ·
                      rfl

theorem cell22_1748466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1748466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748466 prefixEnd_1748466 := by exact prefixLift 1748466
  have htrace : WordTrace (prefixWord ++ tailWord_1748466) baseStart_1748466 baseEnd_1748466 := by
    simpa [prefixWord, tailWord_1748466, baseEnd_1748466] using wordTrace_append hprefix tailTrace_1748466
  have hstable : (prefixWord ++ tailWord_1748466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748466).length < 2 ^ (prefixWord ++ tailWord_1748466).sum := by decide
  have hdescent : baseEnd_1748466 < baseStart_1748466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748477 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1748477 : Nat := 118140960795 + 1748477 * 2 ^ 59
def prefixEnd_1748477 : Nat := 4983230072969 + 3 ^ 40 * 1748477 * 2
def baseEnd_1748477 : Nat := 598539409554307206264271

theorem tailTrace_1748477 : CollatzResearch.WordTrace tailWord_1748477 prefixEnd_1748477 598539409554307206264271 := by
  unfold tailWord_1748477
  simp only [CollatzResearch.WordTrace]
  refine ⟨63772195286573919942667685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42514796857715946628445123 63772195286573919942667685)
  ·
    refine ⟨11957286616232609989250191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63772195286573919942667685 11957286616232609989250191)
    ·
      refine ⟨17935929924348914983875287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11957286616232609989250191 17935929924348914983875287)
      ·
        refine ⟨26903894886523372475812931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17935929924348914983875287 26903894886523372475812931)
        ·
          refine ⟨40355842329785058713719397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26903894886523372475812931 40355842329785058713719397)
          ·
            refine ⟨7566720436834698508822387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40355842329785058713719397 7566720436834698508822387)
            ·
              refine ⟨11350080655252047763233581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566720436834698508822387 11350080655252047763233581)
              ·
                refine ⟨4256280245719517911212593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11350080655252047763233581 4256280245719517911212593)
                ·
                  refine ⟨3192210184289638433409445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4256280245719517911212593 3192210184289638433409445)
                  ·
                    refine ⟨598539409554307206264271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192210184289638433409445 598539409554307206264271)
                    ·
                      rfl

theorem cell22_1748477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1748477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748477 prefixEnd_1748477 := by exact prefixLift 1748477
  have htrace : WordTrace (prefixWord ++ tailWord_1748477) baseStart_1748477 baseEnd_1748477 := by
    simpa [prefixWord, tailWord_1748477, baseEnd_1748477] using wordTrace_append hprefix tailTrace_1748477
  have hstable : (prefixWord ++ tailWord_1748477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748477).length < 2 ^ (prefixWord ++ tailWord_1748477).sum := by decide
  have hdescent : baseEnd_1748477 < baseStart_1748477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748492 : List Nat := [2, 2, 1, 2, 6, 9]
def baseStart_1748492 : Nat := 118140960795 + 1748492 * 2 ^ 59
def prefixEnd_1748492 : Nat := 4983230072969 + 3 ^ 40 * 1748492 * 2
def baseEnd_1748492 : Nat := 7389438819269779841225

theorem tailTrace_1748492 : CollatzResearch.WordTrace tailWord_1748492 prefixEnd_1748492 7389438819269779841225 := by
  unfold tailWord_1748492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31886371190759788752231865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42515161587679718336309153 31886371190759788752231865)
  ·
    refine ⟨23914778393069841564173899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31886371190759788752231865 23914778393069841564173899)
    ·
      refine ⟨35872167589604762346260849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23914778393069841564173899 35872167589604762346260849)
      ·
        refine ⟨26904125692203571759695637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35872167589604762346260849 26904125692203571759695637)
        ·
          refine ⟨1261130891822042426235733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26904125692203571759695637 1261130891822042426235733)
          ·
            refine ⟨7389438819269779841225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1261130891822042426235733 7389438819269779841225)
            ·
              rfl

theorem cell22_1748492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 9].length) (baseStart_1748492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748492 prefixEnd_1748492 := by exact prefixLift 1748492
  have htrace : WordTrace (prefixWord ++ tailWord_1748492) baseStart_1748492 baseEnd_1748492 := by
    simpa [prefixWord, tailWord_1748492, baseEnd_1748492] using wordTrace_append hprefix tailTrace_1748492
  have hstable : (prefixWord ++ tailWord_1748492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748492).length < 2 ^ (prefixWord ++ tailWord_1748492).sum := by decide
  have hdescent : baseEnd_1748492 < baseStart_1748492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748522 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1748522 : Nat := 118140960795 + 1748522 * 2 ^ 59
def prefixEnd_1748522 : Nat := 4983230072969 + 3 ^ 40 * 1748522 * 2
def baseEnd_1748522 : Nat := 598554813973942088889133

theorem tailTrace_1748522 : CollatzResearch.WordTrace tailWord_1748522 prefixEnd_1748522 598554813973942088889133 := by
  unfold tailWord_1748522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943459142852723157013955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42515891047607261752037213 15943459142852723157013955)
  ·
    refine ⟨23915188714279084735520933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15943459142852723157013955 23915188714279084735520933)
    ·
      refine ⟨4484097883927328387910175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23915188714279084735520933 4484097883927328387910175)
      ·
        refine ⟨6726146825890992581865263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484097883927328387910175 6726146825890992581865263)
        ·
          refine ⟨10089220238836488872797895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726146825890992581865263 10089220238836488872797895)
          ·
            refine ⟨15133830358254733309196843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089220238836488872797895 15133830358254733309196843)
            ·
              refine ⟨22700745537382099963795265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15133830358254733309196843 22700745537382099963795265)
              ·
                refine ⟨17025559153036574972846449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22700745537382099963795265 17025559153036574972846449)
                ·
                  refine ⟨12769169364777431229634837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17025559153036574972846449 12769169364777431229634837)
                  ·
                    refine ⟨598554813973942088889133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12769169364777431229634837 598554813973942088889133)
                    ·
                      rfl

theorem cell22_1748522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1748522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748522 prefixEnd_1748522 := by exact prefixLift 1748522
  have htrace : WordTrace (prefixWord ++ tailWord_1748522) baseStart_1748522 baseEnd_1748522 := by
    simpa [prefixWord, tailWord_1748522, baseEnd_1748522] using wordTrace_append hprefix tailTrace_1748522
  have hstable : (prefixWord ++ tailWord_1748522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748522).length < 2 ^ (prefixWord ++ tailWord_1748522).sum := by decide
  have hdescent : baseEnd_1748522 < baseStart_1748522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748631 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1748631 : Nat := 118140960795 + 1748631 * 2 ^ 59
def prefixEnd_1748631 : Nat := 4983230072969 + 3 ^ 40 * 1748631 * 2
def baseEnd_1748631 : Nat := 598592126901502137913799

theorem tailTrace_1748631 : CollatzResearch.WordTrace tailWord_1748631 prefixEnd_1748631 598592126901502137913799 := by
  unfold tailWord_1748631
  simp only [CollatzResearch.WordTrace]
  refine ⟨63777812128016004243773747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42518541418677336162515831 63777812128016004243773747)
  ·
    refine ⟨95666718192024006365660621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63777812128016004243773747 95666718192024006365660621)
    ·
      refine ⟨35875019322009002387122733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95666718192024006365660621 35875019322009002387122733)
      ·
        refine ⟨13453132245753375895171025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35875019322009002387122733 13453132245753375895171025)
        ·
          refine ⟨10089849184315031921378269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13453132245753375895171025 10089849184315031921378269)
          ·
            refine ⟨3783693444118136970516851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10089849184315031921378269 3783693444118136970516851)
            ·
              refine ⟨5675540166177205455775277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783693444118136970516851 5675540166177205455775277)
              ·
                refine ⟨2128327562316452045915729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5675540166177205455775277 2128327562316452045915729)
                ·
                  refine ⟨1596245671737339034436797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128327562316452045915729 1596245671737339034436797)
                  ·
                    refine ⟨598592126901502137913799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1596245671737339034436797 598592126901502137913799)
                    ·
                      rfl

theorem cell22_1748631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1748631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748631 prefixEnd_1748631 := by exact prefixLift 1748631
  have htrace : WordTrace (prefixWord ++ tailWord_1748631) baseStart_1748631 baseEnd_1748631 := by
    simpa [prefixWord, tailWord_1748631, baseEnd_1748631] using wordTrace_append hprefix tailTrace_1748631
  have hstable : (prefixWord ++ tailWord_1748631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748631).length < 2 ^ (prefixWord ++ tailWord_1748631).sum := by decide
  have hdescent : baseEnd_1748631 < baseStart_1748631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748676 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1748676 : Nat := 118140960795 + 1748676 * 2 ^ 59
def prefixEnd_1748676 : Nat := 4983230072969 + 3 ^ 40 * 1748676 * 2
def baseEnd_1748676 : Nat := 598607531321137020538661

theorem tailTrace_1748676 : CollatzResearch.WordTrace tailWord_1748676 prefixEnd_1748676 598607531321137020538661 := by
  unfold tailWord_1748676
  simp only [CollatzResearch.WordTrace]
  refine ⟨31889726706426488464580941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42519635608568651286107921 31889726706426488464580941)
  ·
    refine ⟨11958647514909933174217853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31889726706426488464580941 11958647514909933174217853)
    ·
      refine ⟨4484492818091224940331695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11958647514909933174217853 4484492818091224940331695)
      ·
        refine ⟨6726739227136837410497543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484492818091224940331695 6726739227136837410497543)
        ·
          refine ⟨10090108840705256115746315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726739227136837410497543 10090108840705256115746315)
          ·
            refine ⟨15135163261057884173619473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090108840705256115746315 15135163261057884173619473)
            ·
              refine ⟨11351372445793413130214605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15135163261057884173619473 11351372445793413130214605)
              ·
                refine ⟨4256764667172529923830477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11351372445793413130214605 4256764667172529923830477)
                ·
                  refine ⟨1596286750189698721436429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4256764667172529923830477 1596286750189698721436429)
                  ·
                    refine ⟨598607531321137020538661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1596286750189698721436429 598607531321137020538661)
                    ·
                      rfl

theorem cell22_1748676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1748676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748676 prefixEnd_1748676 := by exact prefixLift 1748676
  have htrace : WordTrace (prefixWord ++ tailWord_1748676) baseStart_1748676 baseEnd_1748676 := by
    simpa [prefixWord, tailWord_1748676, baseEnd_1748676] using wordTrace_append hprefix tailTrace_1748676
  have hstable : (prefixWord ++ tailWord_1748676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748676).length < 2 ^ (prefixWord ++ tailWord_1748676).sum := by decide
  have hdescent : baseEnd_1748676 < baseStart_1748676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748678 : List Nat := [6, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1748678 : Nat := 118140960795 + 1748678 * 2 ^ 59
def prefixEnd_1748678 : Nat := 4983230072969 + 3 ^ 40 * 1748678 * 2
def baseEnd_1748678 : Nat := 66512023995778853554295

theorem tailTrace_1748678 : CollatzResearch.WordTrace tailWord_1748678 prefixEnd_1748678 66512023995778853554295 := by
  unfold tailWord_1748678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993110198713929102210459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42519684239230487513823125 1993110198713929102210459)
  ·
    refine ⟨2989665298070893653315689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993110198713929102210459 2989665298070893653315689)
    ·
      refine ⟨2242248973553170239986767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989665298070893653315689 2242248973553170239986767)
      ·
        refine ⟨3363373460329755359980151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242248973553170239986767 3363373460329755359980151)
        ·
          refine ⟨5045060190494633039970227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363373460329755359980151 5045060190494633039970227)
          ·
            refine ⟨7567590285741949559955341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045060190494633039970227 7567590285741949559955341)
            ·
              refine ⟨2837846357153231084983253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7567590285741949559955341 2837846357153231084983253)
              ·
                refine ⟨66512023995778853554295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2837846357153231084983253 66512023995778853554295)
                ·
                  rfl

theorem cell22_1748678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1748678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748678 prefixEnd_1748678 := by exact prefixLift 1748678
  have htrace : WordTrace (prefixWord ++ tailWord_1748678) baseStart_1748678 baseEnd_1748678 := by
    simpa [prefixWord, tailWord_1748678, baseEnd_1748678] using wordTrace_append hprefix tailTrace_1748678
  have hstable : (prefixWord ++ tailWord_1748678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748678).length < 2 ^ (prefixWord ++ tailWord_1748678).sum := by decide
  have hdescent : baseEnd_1748678 < baseStart_1748678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748689 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 5]
def baseStart_1748689 : Nat := 118140960795 + 1748689 * 2 ^ 59
def prefixEnd_1748689 : Nat := 4983230072969 + 3 ^ 40 * 1748689 * 2
def baseEnd_1748689 : Nat := 199537327162269773321207

theorem tailTrace_1748689 : CollatzResearch.WordTrace tailWord_1748689 prefixEnd_1748689 199537327162269773321207 := by
  unfold tailWord_1748689
  simp only [CollatzResearch.WordTrace]
  refine ⟨63779927561805880149385121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42519951707870586766256747 63779927561805880149385121)
  ·
    refine ⟨47834945671354410112038841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63779927561805880149385121 47834945671354410112038841)
    ·
      refine ⟨35876209253515807584029131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47834945671354410112038841 35876209253515807584029131)
      ·
        refine ⟨53814313880273711376043697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35876209253515807584029131 53814313880273711376043697)
        ·
          refine ⟨40360735410205283532032773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53814313880273711376043697 40360735410205283532032773)
          ·
            refine ⟨7567637889413490662256145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40360735410205283532032773 7567637889413490662256145)
            ·
              refine ⟨5675728417060117996692109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567637889413490662256145 5675728417060117996692109)
              ·
                refine ⟨2128398156397544248759541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5675728417060117996692109 2128398156397544248759541)
                ·
                  refine ⟨199537327162269773321207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2128398156397544248759541 199537327162269773321207)
                  ·
                    rfl

theorem cell22_1748689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_1748689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748689 prefixEnd_1748689 := by exact prefixLift 1748689
  have htrace : WordTrace (prefixWord ++ tailWord_1748689) baseStart_1748689 baseEnd_1748689 := by
    simpa [prefixWord, tailWord_1748689, baseEnd_1748689] using wordTrace_append hprefix tailTrace_1748689
  have hstable : (prefixWord ++ tailWord_1748689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748689).length < 2 ^ (prefixWord ++ tailWord_1748689).sum := by decide
  have hdescent : baseEnd_1748689 < baseStart_1748689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748764 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1748764 : Nat := 118140960795 + 1748764 * 2 ^ 59
def prefixEnd_1748764 : Nat := 4983230072969 + 3 ^ 40 * 1748764 * 2
def baseEnd_1748764 : Nat := 598637655519534124338391

theorem tailTrace_1748764 : CollatzResearch.WordTrace tailWord_1748764 prefixEnd_1748764 598637655519534124338391 := by
  unfold tailWord_1748764
  simp only [CollatzResearch.WordTrace]
  refine ⟨31891331518267083979182673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42521775357689445305576897 31891331518267083979182673)
  ·
    refine ⟨23918498638700312984387005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31891331518267083979182673 23918498638700312984387005)
    ·
      refine ⟨8969436989512617369145127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23918498638700312984387005 8969436989512617369145127)
      ·
        refine ⟨13454155484268926053717691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8969436989512617369145127 13454155484268926053717691)
        ·
          refine ⟨20181233226403389080576537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13454155484268926053717691 20181233226403389080576537)
          ·
            refine ⟨15135924919802541810432403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20181233226403389080576537 15135924919802541810432403)
            ·
              refine ⟨22703887379703812715648605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15135924919802541810432403 22703887379703812715648605)
              ·
                refine ⟨8513957767388929768368227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22703887379703812715648605 8513957767388929768368227)
                ·
                  refine ⟨12770936651083394652552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513957767388929768368227 12770936651083394652552341)
                  ·
                    refine ⟨598637655519534124338391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12770936651083394652552341 598637655519534124338391)
                    ·
                      rfl

theorem cell22_1748764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1748764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748764 prefixEnd_1748764 := by exact prefixLift 1748764
  have htrace : WordTrace (prefixWord ++ tailWord_1748764) baseStart_1748764 baseEnd_1748764 := by
    simpa [prefixWord, tailWord_1748764, baseEnd_1748764] using wordTrace_append hprefix tailTrace_1748764
  have hstable : (prefixWord ++ tailWord_1748764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748764).length < 2 ^ (prefixWord ++ tailWord_1748764).sum := by decide
  have hdescent : baseEnd_1748764 < baseStart_1748764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748903 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 6]
def baseStart_1748903 : Nat := 118140960795 + 1748903 * 2 ^ 59
def prefixEnd_1748903 : Nat := 4983230072969 + 3 ^ 40 * 1748903 * 2
def baseEnd_1748903 : Nat := 199561746020061365037655

theorem tailTrace_1748903 : CollatzResearch.WordTrace tailWord_1748903 prefixEnd_1748903 199561746020061365037655 := by
  unfold tailWord_1748903
  simp only [CollatzResearch.WordTrace]
  refine ⟨63787732783030594697675363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42525155188687063131783575 63787732783030594697675363)
  ·
    refine ⟨95681599174545892046513045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63787732783030594697675363 95681599174545892046513045)
    ·
      refine ⟨4485074961306838689680299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95681599174545892046513045 4485074961306838689680299)
      ·
        refine ⟨6727612441960258034520449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485074961306838689680299 6727612441960258034520449)
        ·
          refine ⟨5045709331470193525890337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727612441960258034520449 5045709331470193525890337)
          ·
            refine ⟨3784281998602645144417753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045709331470193525890337 3784281998602645144417753)
            ·
              refine ⟨2838211498951983858313315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3784281998602645144417753 2838211498951983858313315)
              ·
                refine ⟨4257317248427975787469973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838211498951983858313315 4257317248427975787469973)
                ·
                  refine ⟨199561746020061365037655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4257317248427975787469973 199561746020061365037655)
                  ·
                    rfl

theorem cell22_1748903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 6].length) (baseStart_1748903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1748903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1748903 prefixEnd_1748903 := by exact prefixLift 1748903
  have htrace : WordTrace (prefixWord ++ tailWord_1748903) baseStart_1748903 baseEnd_1748903 := by
    simpa [prefixWord, tailWord_1748903, baseEnd_1748903] using wordTrace_append hprefix tailTrace_1748903
  have hstable : (prefixWord ++ tailWord_1748903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748903).length < 2 ^ (prefixWord ++ tailWord_1748903).sum := by decide
  have hdescent : baseEnd_1748903 < baseStart_1748903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749038 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_1749038 : Nat := 118140960795 + 1749038 * 2 ^ 59
def prefixEnd_1749038 : Nat := 4983230072969 + 3 ^ 40 * 1749038 * 2
def baseEnd_1749038 : Nat := 199577150439696247662517

theorem tailTrace_1749038 : CollatzResearch.WordTrace tailWord_1749038 prefixEnd_1749038 199577150439696247662517 := by
  unfold tailWord_1749038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974082079692689094229971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42528437758361008502559845 7974082079692689094229971)
  ·
    refine ⟨11961123119539033641344957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7974082079692689094229971 11961123119539033641344957)
    ·
      refine ⟨4485421169827137615504359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11961123119539033641344957 4485421169827137615504359)
      ·
        refine ⟨6728131754740706423256539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485421169827137615504359 6728131754740706423256539)
        ·
          refine ⟨10092197632111059634884809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728131754740706423256539 10092197632111059634884809)
          ·
            refine ⟨7569148224083294726163607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10092197632111059634884809 7569148224083294726163607)
            ·
              refine ⟨11353722336124942089245411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569148224083294726163607 11353722336124942089245411)
              ·
                refine ⟨17030583504187413133868117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353722336124942089245411 17030583504187413133868117)
                ·
                  refine ⟨199577150439696247662517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17030583504187413133868117 199577150439696247662517)
                  ·
                    rfl

theorem cell22_1749038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_1749038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749038 prefixEnd_1749038 := by exact prefixLift 1749038
  have htrace : WordTrace (prefixWord ++ tailWord_1749038) baseStart_1749038 baseEnd_1749038 := by
    simpa [prefixWord, tailWord_1749038, baseEnd_1749038] using wordTrace_append hprefix tailTrace_1749038
  have hstable : (prefixWord ++ tailWord_1749038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749038).length < 2 ^ (prefixWord ++ tailWord_1749038).sum := by decide
  have hdescent : baseEnd_1749038 < baseStart_1749038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749051 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_1749051 : Nat := 118140960795 + 1749051 * 2 ^ 59
def prefixEnd_1749051 : Nat := 4983230072969 + 3 ^ 40 * 1749051 * 2
def baseEnd_1749051 : Nat := 598735901484761042412511

theorem tailTrace_1749051 : CollatzResearch.WordTrace tailWord_1749051 prefixEnd_1749051 598735901484761042412511 := by
  unfold tailWord_1749051
  simp only [CollatzResearch.WordTrace]
  refine ⟨63793130786494415974063007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42528753857662943982708671 63793130786494415974063007)
  ·
    refine ⟨95689696179741623961094511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63793130786494415974063007 95689696179741623961094511)
    ·
      refine ⟨143534544269612435941641767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95689696179741623961094511 143534544269612435941641767)
      ·
        refine ⟨215301816404418653912462651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143534544269612435941641767 215301816404418653912462651)
        ·
          refine ⟨322952724606627980868693977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215301816404418653912462651 322952724606627980868693977)
          ·
            refine ⟨242214543454970985651520483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322952724606627980868693977 242214543454970985651520483)
            ·
              refine ⟨363321815182456478477280725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242214543454970985651520483 363321815182456478477280725)
              ·
                refine ⟨8515355043338823714311267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 363321815182456478477280725 8515355043338823714311267)
                ·
                  refine ⟨12773032565008235571466901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515355043338823714311267 12773032565008235571466901)
                  ·
                    refine ⟨598735901484761042412511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12773032565008235571466901 598735901484761042412511)
                    ·
                      rfl

theorem cell22_1749051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_1749051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749051 prefixEnd_1749051 := by exact prefixLift 1749051
  have htrace : WordTrace (prefixWord ++ tailWord_1749051) baseStart_1749051 baseEnd_1749051 := by
    simpa [prefixWord, tailWord_1749051, baseEnd_1749051] using wordTrace_append hprefix tailTrace_1749051
  have hstable : (prefixWord ++ tailWord_1749051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749051).length < 2 ^ (prefixWord ++ tailWord_1749051).sum := by decide
  have hdescent : baseEnd_1749051 < baseStart_1749051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749053 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1749053 : Nat := 118140960795 + 1749053 * 2 ^ 59
def prefixEnd_1749053 : Nat := 4983230072969 + 3 ^ 40 * 1749053 * 2
def baseEnd_1749053 : Nat := 598736586125633703862505

theorem tailTrace_1749053 : CollatzResearch.WordTrace tailWord_1749053 prefixEnd_1749053 598736586125633703862505 := by
  unfold tailWord_1749053
  simp only [CollatzResearch.WordTrace]
  refine ⟨63793203732487170315635813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42528802488324780210423875 63793203732487170315635813)
  ·
    refine ⟨11961225699841344434181715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63793203732487170315635813 11961225699841344434181715)
    ·
      refine ⟨17941838549762016651272573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11961225699841344434181715 17941838549762016651272573)
      ·
        refine ⟨6728189456160756244227215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17941838549762016651272573 6728189456160756244227215)
        ·
          refine ⟨10092284184241134366340823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728189456160756244227215 10092284184241134366340823)
          ·
            refine ⟨15138426276361701549511235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10092284184241134366340823 15138426276361701549511235)
            ·
              refine ⟨22707639414542552324266853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15138426276361701549511235 22707639414542552324266853)
              ·
                refine ⟨4257682390226728560800035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22707639414542552324266853 4257682390226728560800035)
                ·
                  refine ⟨6386523585340092841200053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257682390226728560800035 6386523585340092841200053)
                  ·
                    refine ⟨598736586125633703862505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6386523585340092841200053 598736586125633703862505)
                    ·
                      rfl

theorem cell22_1749053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1749053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749053 prefixEnd_1749053 := by exact prefixLift 1749053
  have htrace : WordTrace (prefixWord ++ tailWord_1749053) baseStart_1749053 baseEnd_1749053 := by
    simpa [prefixWord, tailWord_1749053, baseEnd_1749053] using wordTrace_append hprefix tailTrace_1749053
  have hstable : (prefixWord ++ tailWord_1749053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749053).length < 2 ^ (prefixWord ++ tailWord_1749053).sum := by decide
  have hdescent : baseEnd_1749053 < baseStart_1749053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749057 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1749057 : Nat := 118140960795 + 1749057 * 2 ^ 59
def prefixEnd_1749057 : Nat := 4983230072969 + 3 ^ 40 * 1749057 * 2
def baseEnd_1749057 : Nat := 598737955407379026762493

theorem tailTrace_1749057 : CollatzResearch.WordTrace tailWord_1749057 prefixEnd_1749057 598737955407379026762493 := by
  unfold tailWord_1749057
  simp only [CollatzResearch.WordTrace]
  refine ⟨63793349624472678998781425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42528899749648452665854283 63793349624472678998781425)
  ·
    refine ⟨47845012218354509249086069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63793349624472678998781425 47845012218354509249086069)
    ·
      refine ⟨4485469895470735242101819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47845012218354509249086069 4485469895470735242101819)
      ·
        refine ⟨6728204843206102863152729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485469895470735242101819 6728204843206102863152729)
        ·
          refine ⟨5046153632404577147364547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6728204843206102863152729 5046153632404577147364547)
          ·
            refine ⟨7569230448606865721046821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046153632404577147364547 7569230448606865721046821)
            ·
              refine ⟨1419230709113787322696279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7569230448606865721046821 1419230709113787322696279)
              ·
                refine ⟨2128846063670680984044419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419230709113787322696279 2128846063670680984044419)
                ·
                  refine ⟨3193269095506021476066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128846063670680984044419 3193269095506021476066629)
                  ·
                    refine ⟨598737955407379026762493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193269095506021476066629 598737955407379026762493)
                    ·
                      rfl

theorem cell22_1749057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1749057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749057 prefixEnd_1749057 := by exact prefixLift 1749057
  have htrace : WordTrace (prefixWord ++ tailWord_1749057) baseStart_1749057 baseEnd_1749057 := by
    simpa [prefixWord, tailWord_1749057, baseEnd_1749057] using wordTrace_append hprefix tailTrace_1749057
  have hstable : (prefixWord ++ tailWord_1749057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749057).length < 2 ^ (prefixWord ++ tailWord_1749057).sum := by decide
  have hdescent : baseEnd_1749057 < baseStart_1749057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749068 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_1749068 : Nat := 118140960795 + 1749068 * 2 ^ 59
def prefixEnd_1749068 : Nat := 4983230072969 + 3 ^ 40 * 1749068 * 2
def baseEnd_1749068 : Nat := 598741720932178664737459

theorem tailTrace_1749068 : CollatzResearch.WordTrace tailWord_1749068 prefixEnd_1749068 598741720932178664737459 := by
  unfold tailWord_1749068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31896875413716413938715929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42529167218288551918287905 31896875413716413938715929)
  ·
    refine ⟨23922656560287310454036947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31896875413716413938715929 23922656560287310454036947)
    ·
      refine ⟨35883984840430965681055421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23922656560287310454036947 35883984840430965681055421)
      ·
        refine ⟨13456494315161612130395783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35883984840430965681055421 13456494315161612130395783)
        ·
          refine ⟨20184741472742418195593675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13456494315161612130395783 20184741472742418195593675)
          ·
            refine ⟨30277112209113627293390513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20184741472742418195593675 30277112209113627293390513)
            ·
              refine ⟨22707834156835220470042885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30277112209113627293390513 22707834156835220470042885)
              ·
                refine ⟨4257718904406603838133041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22707834156835220470042885 4257718904406603838133041)
                ·
                  refine ⟨3193289178304952878599781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4257718904406603838133041 3193289178304952878599781)
                  ·
                    refine ⟨598741720932178664737459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193289178304952878599781 598741720932178664737459)
                    ·
                      rfl

theorem cell22_1749068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_1749068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749068 prefixEnd_1749068 := by exact prefixLift 1749068
  have htrace : WordTrace (prefixWord ++ tailWord_1749068) baseStart_1749068 baseEnd_1749068 := by
    simpa [prefixWord, tailWord_1749068, baseEnd_1749068] using wordTrace_append hprefix tailTrace_1749068
  have hstable : (prefixWord ++ tailWord_1749068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749068).length < 2 ^ (prefixWord ++ tailWord_1749068).sum := by decide
  have hdescent : baseEnd_1749068 < baseStart_1749068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749070 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1749070 : Nat := 118140960795 + 1749070 * 2 ^ 59
def prefixEnd_1749070 : Nat := 4983230072969 + 3 ^ 40 * 1749070 * 2
def baseEnd_1749070 : Nat := 598742405573051326187453

theorem tailTrace_1749070 : CollatzResearch.WordTrace tailWord_1749070 prefixEnd_1749070 598742405573051326187453 := by
  unfold tailWord_1749070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974227971678197777375583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42529215848950388146003109 7974227971678197777375583)
  ·
    refine ⟨11961341957517296666063375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7974227971678197777375583 11961341957517296666063375)
    ·
      refine ⟨17942012936275944999095063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11961341957517296666063375 17942012936275944999095063)
      ·
        refine ⟨26913019404413917498642595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17942012936275944999095063 26913019404413917498642595)
        ·
          refine ⟨40369529106620876247963893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26913019404413917498642595 40369529106620876247963893)
          ·
            refine ⟨3784643353745707148246615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40369529106620876247963893 3784643353745707148246615)
            ·
              refine ⟨5676965030618560722369923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784643353745707148246615 5676965030618560722369923)
              ·
                refine ⟨8515447545927841083554885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676965030618560722369923 8515447545927841083554885)
                ·
                  refine ⟨1596646414861470203166541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8515447545927841083554885 1596646414861470203166541)
                  ·
                    refine ⟨598742405573051326187453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1596646414861470203166541 598742405573051326187453)
                    ·
                      rfl

theorem cell22_1749070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1749070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749070 prefixEnd_1749070 := by exact prefixLift 1749070
  have htrace : WordTrace (prefixWord ++ tailWord_1749070) baseStart_1749070 baseEnd_1749070 := by
    simpa [prefixWord, tailWord_1749070, baseEnd_1749070] using wordTrace_append hprefix tailTrace_1749070
  have hstable : (prefixWord ++ tailWord_1749070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749070).length < 2 ^ (prefixWord ++ tailWord_1749070).sum := by decide
  have hdescent : baseEnd_1749070 < baseStart_1749070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749085 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1749085 : Nat := 118140960795 + 1749085 * 2 ^ 59
def prefixEnd_1749085 : Nat := 4983230072969 + 3 ^ 40 * 1749085 * 2
def baseEnd_1749085 : Nat := 598747540379596287062407

theorem tailTrace_1749085 : CollatzResearch.WordTrace tailWord_1749085 prefixEnd_1749085 598747540379596287062407 := by
  unfold tailWord_1749085
  simp only [CollatzResearch.WordTrace]
  refine ⟨63794370868371239780800709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42529580578914159853867139 63794370868371239780800709)
  ·
    refine ⟨11961444537819607458900133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63794370868371239780800709 11961444537819607458900133)
    ·
      refine ⟨2242770850841176398543775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11961444537819607458900133 2242770850841176398543775)
      ·
        refine ⟨3364156276261764597815663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242770850841176398543775 3364156276261764597815663)
        ·
          refine ⟨5046234414392646896723495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364156276261764597815663 5046234414392646896723495)
          ·
            refine ⟨7569351621588970345085243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046234414392646896723495 7569351621588970345085243)
            ·
              refine ⟨11354027432383455517627865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569351621588970345085243 11354027432383455517627865)
              ·
                refine ⟨8515520574287591638220899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11354027432383455517627865 8515520574287591638220899)
                ·
                  refine ⟨12773280861431387457331349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515520574287591638220899 12773280861431387457331349)
                  ·
                    refine ⟨598747540379596287062407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12773280861431387457331349 598747540379596287062407)
                    ·
                      rfl

theorem cell22_1749085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1749085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749085 prefixEnd_1749085 := by exact prefixLift 1749085
  have htrace : WordTrace (prefixWord ++ tailWord_1749085) baseStart_1749085 baseEnd_1749085 := by
    simpa [prefixWord, tailWord_1749085, baseEnd_1749085] using wordTrace_append hprefix tailTrace_1749085
  have hstable : (prefixWord ++ tailWord_1749085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749085).length < 2 ^ (prefixWord ++ tailWord_1749085).sum := by decide
  have hdescent : baseEnd_1749085 < baseStart_1749085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749100 : List Nat := [2, 2, 1, 1, 3, 5, 2, 6]
def baseStart_1749100 : Nat := 118140960795 + 1749100 * 2 ^ 59
def prefixEnd_1749100 : Nat := 4983230072969 + 3 ^ 40 * 1749100 * 2
def baseEnd_1749100 : Nat := 66528075020682360881929

theorem tailTrace_1749100 : CollatzResearch.WordTrace tailWord_1749100 prefixEnd_1749100 66528075020682360881929 := by
  unfold tailWord_1749100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31897458981658448671298377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42529945308877931561731169 31897458981658448671298377)
  ·
    refine ⟨23923094236243836503473783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31897458981658448671298377 23923094236243836503473783)
    ·
      refine ⟨35884641354365754755210675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23923094236243836503473783 35884641354365754755210675)
      ·
        refine ⟨53826962031548632132816013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35884641354365754755210675 53826962031548632132816013)
        ·
          refine ⟨20185110761830737049806005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53826962031548632132816013 20185110761830737049806005)
          ·
            refine ⟨1892354133921631598419313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20185110761830737049806005 1892354133921631598419313)
            ·
              refine ⟨1419265600441223698814485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892354133921631598419313 1419265600441223698814485)
              ·
                refine ⟨66528075020682360881929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1419265600441223698814485 66528075020682360881929)
                ·
                  rfl

theorem cell22_1749100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_1749100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749100 prefixEnd_1749100 := by exact prefixLift 1749100
  have htrace : WordTrace (prefixWord ++ tailWord_1749100) baseStart_1749100 baseEnd_1749100 := by
    simpa [prefixWord, tailWord_1749100, baseEnd_1749100] using wordTrace_append hprefix tailTrace_1749100
  have hstable : (prefixWord ++ tailWord_1749100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749100).length < 2 ^ (prefixWord ++ tailWord_1749100).sum := by decide
  have hdescent : baseEnd_1749100 < baseStart_1749100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749248 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_1749248 : Nat := 118140960795 + 1749248 * 2 ^ 59
def prefixEnd_1749248 : Nat := 4983230072969 + 3 ^ 40 * 1749248 * 2
def baseEnd_1749248 : Nat := 598803338610718195236907

theorem tailTrace_1749248 : CollatzResearch.WordTrace tailWord_1749248 prefixEnd_1749248 598803338610718195236907 := by
  unfold tailWord_1749248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900157983390359309492199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42533543977853812412656265 31900157983390359309492199)
  ·
    refine ⟨47850236975085538964238299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31900157983390359309492199 47850236975085538964238299)
    ·
      refine ⟨71775355462628308446357449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47850236975085538964238299 71775355462628308446357449)
      ·
        refine ⟨53831516596971231334768087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71775355462628308446357449 53831516596971231334768087)
        ·
          refine ⟨80747274895456847002152131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53831516596971231334768087 80747274895456847002152131)
          ·
            refine ⟨121120912343185270503228197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80747274895456847002152131 121120912343185270503228197)
            ·
              refine ⟨22710171064347238219355287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121120912343185270503228197 22710171064347238219355287)
              ·
                refine ⟨34065256596520857329032931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22710171064347238219355287 34065256596520857329032931)
                ·
                  refine ⟨51097884894781285993549397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34065256596520857329032931 51097884894781285993549397)
                  ·
                    refine ⟨598803338610718195236907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51097884894781285993549397 598803338610718195236907)
                    ·
                      rfl

theorem cell22_1749248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_1749248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749248 prefixEnd_1749248 := by exact prefixLift 1749248
  have htrace : WordTrace (prefixWord ++ tailWord_1749248) baseStart_1749248 baseEnd_1749248 := by
    simpa [prefixWord, tailWord_1749248, baseEnd_1749248] using wordTrace_append hprefix tailTrace_1749248
  have hstable : (prefixWord ++ tailWord_1749248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749248).length < 2 ^ (prefixWord ++ tailWord_1749248).sum := by decide
  have hdescent : baseEnd_1749248 < baseStart_1749248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749280 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_1749280 : Nat := 118140960795 + 1749280 * 2 ^ 59
def prefixEnd_1749280 : Nat := 4983230072969 + 3 ^ 40 * 1749280 * 2
def baseEnd_1749280 : Nat := 199604764288226926145603

theorem tailTrace_1749280 : CollatzResearch.WordTrace tailWord_1749280 prefixEnd_1749280 199604764288226926145603 := by
  unfold tailWord_1749280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900741551332394042074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42534322068443192056099529 31900741551332394042074647)
  ·
    refine ⟨47851112326998591063111971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31900741551332394042074647 47851112326998591063111971)
    ·
      refine ⟨71776668490497886594667957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47851112326998591063111971 71776668490497886594667957)
      ·
        refine ⟨6729062670984176868250121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71776668490497886594667957 6729062670984176868250121)
        ·
          refine ⟨5046797003238132651187591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6729062670984176868250121 5046797003238132651187591)
          ·
            refine ⟨7570195504857198976781387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046797003238132651187591 7570195504857198976781387)
            ·
              refine ⟨11355293257285798465172081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570195504857198976781387 11355293257285798465172081)
              ·
                refine ⟨8516469942964348848879061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11355293257285798465172081 8516469942964348848879061)
                ·
                  refine ⟨199604764288226926145603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8516469942964348848879061 199604764288226926145603)
                  ·
                    rfl

theorem cell22_1749280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_1749280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749280 prefixEnd_1749280 := by exact prefixLift 1749280
  have htrace : WordTrace (prefixWord ++ tailWord_1749280) baseStart_1749280 baseEnd_1749280 := by
    simpa [prefixWord, tailWord_1749280, baseEnd_1749280] using wordTrace_append hprefix tailTrace_1749280
  have hstable : (prefixWord ++ tailWord_1749280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749280).length < 2 ^ (prefixWord ++ tailWord_1749280).sum := by decide
  have hdescent : baseEnd_1749280 < baseStart_1749280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749301 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1749301 : Nat := 118140960795 + 1749301 * 2 ^ 59
def prefixEnd_1749301 : Nat := 4983230072969 + 3 ^ 40 * 1749301 * 2
def baseEnd_1749301 : Nat := 598821481593843723661745

theorem tailTrace_1749301 : CollatzResearch.WordTrace tailWord_1749301 prefixEnd_1749301 598821481593843723661745 := by
  unfold tailWord_1749301
  simp only [CollatzResearch.WordTrace]
  refine ⟨63802249035588708670663757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42534832690392472447109171 63802249035588708670663757)
  ·
    refine ⟨23925843388345765751498909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63802249035588708670663757 23925843388345765751498909)
    ·
      refine ⟨8972191270629662156812091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23925843388345765751498909 8972191270629662156812091)
      ·
        refine ⟨13458286905944493235218137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8972191270629662156812091 13458286905944493235218137)
        ·
          refine ⟨10093715179458369926413603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13458286905944493235218137 10093715179458369926413603)
          ·
            refine ⟨15140572769187554889620405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093715179458369926413603 15140572769187554889620405)
            ·
              refine ⟨1419428697111333270901913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15140572769187554889620405 1419428697111333270901913)
              ·
                refine ⟨1064571522833499953176435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419428697111333270901913 1064571522833499953176435)
                ·
                  refine ⟨1596857284250249929764653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064571522833499953176435 1596857284250249929764653)
                  ·
                    refine ⟨598821481593843723661745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1596857284250249929764653 598821481593843723661745)
                    ·
                      rfl

theorem cell22_1749301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1749301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749301 prefixEnd_1749301 := by exact prefixLift 1749301
  have htrace : WordTrace (prefixWord ++ tailWord_1749301) baseStart_1749301 baseEnd_1749301 := by
    simpa [prefixWord, tailWord_1749301, baseEnd_1749301] using wordTrace_append hprefix tailTrace_1749301
  have hstable : (prefixWord ++ tailWord_1749301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749301).length < 2 ^ (prefixWord ++ tailWord_1749301).sum := by decide
  have hdescent : baseEnd_1749301 < baseStart_1749301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749387 : List Nat := [1, 1, 1, 1, 4, 5, 3, 6]
def baseStart_1749387 : Nat := 118140960795 + 1749387 * 2 ^ 59
def prefixEnd_1749387 : Nat := 4983230072969 + 3 ^ 40 * 1749387 * 2
def baseEnd_1749387 : Nat := 66538991239040907334609

theorem tailTrace_1749387 : CollatzResearch.WordTrace tailWord_1749387 prefixEnd_1749387 66538991239040907334609 := by
  unfold tailWord_1749387
  simp only [CollatzResearch.WordTrace]
  refine ⟨63805385713277145358294415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42536923808851430238862943 63805385713277145358294415)
  ·
    refine ⟨95708078569915718037441623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63805385713277145358294415 95708078569915718037441623)
    ·
      refine ⟨143562117854873577056162435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95708078569915718037441623 143562117854873577056162435)
      ·
        refine ⟨215343176782310365584243653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143562117854873577056162435 215343176782310365584243653)
        ·
          refine ⟨40376845646683193547045685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215343176782310365584243653 40376845646683193547045685)
          ·
            refine ⟨3785329279376549395035533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40376845646683193547045685 3785329279376549395035533)
            ·
              refine ⟨1419498479766206023138325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3785329279376549395035533 1419498479766206023138325)
              ·
                refine ⟨66538991239040907334609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1419498479766206023138325 66538991239040907334609)
                ·
                  rfl

theorem cell22_1749387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 6].length) (baseStart_1749387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749387 prefixEnd_1749387 := by exact prefixLift 1749387
  have htrace : WordTrace (prefixWord ++ tailWord_1749387) baseStart_1749387 baseEnd_1749387 := by
    simpa [prefixWord, tailWord_1749387, baseEnd_1749387] using wordTrace_append hprefix tailTrace_1749387
  have hstable : (prefixWord ++ tailWord_1749387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749387).length < 2 ^ (prefixWord ++ tailWord_1749387).sum := by decide
  have hdescent : baseEnd_1749387 < baseStart_1749387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749445 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1749445 : Nat := 118140960795 + 1749445 * 2 ^ 59
def prefixEnd_1749445 : Nat := 4983230072969 + 3 ^ 40 * 1749445 * 2
def baseEnd_1749445 : Nat := 598870775736675348061303

theorem tailTrace_1749445 : CollatzResearch.WordTrace tailWord_1749445 prefixEnd_1749445 598870775736675348061303 := by
  unfold tailWord_1749445
  simp only [CollatzResearch.WordTrace]
  refine ⟨63807501147067021263905789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42538334098044680842603859 63807501147067021263905789)
  ·
    refine ⟨23927812930150132973964671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63807501147067021263905789 23927812930150132973964671)
    ·
      refine ⟨35891719395225199460947007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23927812930150132973964671 35891719395225199460947007)
      ·
        refine ⟨53837579092837799191420511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35891719395225199460947007 53837579092837799191420511)
        ·
          refine ⟨80756368639256698787130767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53837579092837799191420511 80756368639256698787130767)
          ·
            refine ⟨121134552958885048180696151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80756368639256698787130767 121134552958885048180696151)
            ·
              refine ⟨181701829438327572271044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121134552958885048180696151 181701829438327572271044227)
              ·
                refine ⟨272552744157491358406566341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181701829438327572271044227 272552744157491358406566341)
                ·
                  refine ⟨51103639529529629701231189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272552744157491358406566341 51103639529529629701231189)
                  ·
                    refine ⟨598870775736675348061303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51103639529529629701231189 598870775736675348061303)
                    ·
                      rfl

theorem cell22_1749445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1749445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749445 prefixEnd_1749445 := by exact prefixLift 1749445
  have htrace : WordTrace (prefixWord ++ tailWord_1749445) baseStart_1749445 baseEnd_1749445 := by
    simpa [prefixWord, tailWord_1749445, baseEnd_1749445] using wordTrace_append hprefix tailTrace_1749445
  have hstable : (prefixWord ++ tailWord_1749445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749445).length < 2 ^ (prefixWord ++ tailWord_1749445).sum := by decide
  have hdescent : baseEnd_1749445 < baseStart_1749445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749528 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_1749528 : Nat := 118140960795 + 1749528 * 2 ^ 59
def prefixEnd_1749528 : Nat := 4983230072969 + 3 ^ 40 * 1749528 * 2
def baseEnd_1749528 : Nat := 199633062777630266078683

theorem tailTrace_1749528 : CollatzResearch.WordTrace tailWord_1749528 prefixEnd_1749528 199633062777630266078683 := by
  unfold tailWord_1749528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905264202883163219588619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42540352270510884292784825 31905264202883163219588619)
  ·
    refine ⟨47857896304324744829382929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31905264202883163219588619 47857896304324744829382929)
    ·
      refine ⟨35893422228243558622037197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47857896304324744829382929 35893422228243558622037197)
      ·
        refine ⟨13460033335591334483263949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35893422228243558622037197 13460033335591334483263949)
        ·
          refine ⟨5047512500846750431223981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13460033335591334483263949 5047512500846750431223981)
          ·
            refine ⟨1892817187817531411708993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5047512500846750431223981 1892817187817531411708993)
            ·
              refine ⟨1419612890863148558781745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892817187817531411708993 1419612890863148558781745)
              ·
                refine ⟨1064709668147361419086309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419612890863148558781745 1064709668147361419086309)
                ·
                  refine ⟨199633062777630266078683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064709668147361419086309 199633062777630266078683)
                  ·
                    rfl

theorem cell22_1749528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_1749528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749528 prefixEnd_1749528 := by exact prefixLift 1749528
  have htrace : WordTrace (prefixWord ++ tailWord_1749528) baseStart_1749528 baseEnd_1749528 := by
    simpa [prefixWord, tailWord_1749528, baseEnd_1749528] using wordTrace_append hprefix tailTrace_1749528
  have hstable : (prefixWord ++ tailWord_1749528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749528).length < 2 ^ (prefixWord ++ tailWord_1749528).sum := by decide
  have hdescent : baseEnd_1749528 < baseStart_1749528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749539 : List Nat := [1, 1, 1, 4, 4, 3, 1, 7]
def baseStart_1749539 : Nat := 118140960795 + 1749539 * 2 ^ 59
def prefixEnd_1749539 : Nat := 4983230072969 + 3 ^ 40 * 1749539 * 2
def baseEnd_1749539 : Nat := 66544772650854492912335

theorem tailTrace_1749539 : CollatzResearch.WordTrace tailWord_1749539 prefixEnd_1749539 66544772650854492912335 := by
  unfold tailWord_1749539
  simp only [CollatzResearch.WordTrace]
  refine ⟨63810929608726475317827671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42540619739150983545218447 63810929608726475317827671)
  ·
    refine ⟨95716394413089712976741507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63810929608726475317827671 95716394413089712976741507)
    ·
      refine ⟨143574591619634569465112261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95716394413089712976741507 143574591619634569465112261)
      ·
        refine ⟨26920235928681481774708549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143574591619634569465112261 26920235928681481774708549)
        ·
          refine ⟨5047544236627777832757853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26920235928681481774708549 5047544236627777832757853)
          ·
            refine ⟨1892829088735416687284195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5047544236627777832757853 1892829088735416687284195)
            ·
              refine ⟨2839243633103125030926293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892829088735416687284195 2839243633103125030926293)
              ·
                refine ⟨66544772650854492912335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2839243633103125030926293 66544772650854492912335)
                ·
                  rfl

theorem cell22_1749539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 7].length) (baseStart_1749539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749539 prefixEnd_1749539 := by exact prefixLift 1749539
  have htrace : WordTrace (prefixWord ++ tailWord_1749539) baseStart_1749539 baseEnd_1749539 := by
    simpa [prefixWord, tailWord_1749539, baseEnd_1749539] using wordTrace_append hprefix tailTrace_1749539
  have hstable : (prefixWord ++ tailWord_1749539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749539).length < 2 ^ (prefixWord ++ tailWord_1749539).sum := by decide
  have hdescent : baseEnd_1749539 < baseStart_1749539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749543 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1749543 : Nat := 118140960795 + 1749543 * 2 ^ 59
def prefixEnd_1749543 : Nat := 4983230072969 + 3 ^ 40 * 1749543 * 2
def baseEnd_1749543 : Nat := 598904323139435759111003

theorem tailTrace_1749543 : CollatzResearch.WordTrace tailWord_1749543 prefixEnd_1749543 598904323139435759111003 := by
  unfold tailWord_1749543
  simp only [CollatzResearch.WordTrace]
  refine ⟨63811075500711984000973283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42540717000474656000648855 63811075500711984000973283)
  ·
    refine ⟨95716613251067976001459925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63811075500711984000973283 95716613251067976001459925)
    ·
      refine ⟨2243358123071905687534217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95716613251067976001459925 2243358123071905687534217)
      ·
        refine ⟨1682518592303929265650663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2243358123071905687534217 1682518592303929265650663)
        ·
          refine ⟨2523777888455893898475995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682518592303929265650663 2523777888455893898475995)
          ·
            refine ⟨3785666832683840847713993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523777888455893898475995 3785666832683840847713993)
            ·
              refine ⟨2839250124512880635785495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785666832683840847713993 2839250124512880635785495)
              ·
                refine ⟨4258875186769320953678243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839250124512880635785495 4258875186769320953678243)
                ·
                  refine ⟨6388312780153981430517365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258875186769320953678243 6388312780153981430517365)
                  ·
                    refine ⟨598904323139435759111003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6388312780153981430517365 598904323139435759111003)
                    ·
                      rfl

theorem cell22_1749543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1749543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749543 prefixEnd_1749543 := by exact prefixLift 1749543
  have htrace : WordTrace (prefixWord ++ tailWord_1749543) baseStart_1749543 baseEnd_1749543 := by
    simpa [prefixWord, tailWord_1749543, baseEnd_1749543] using wordTrace_append hprefix tailTrace_1749543
  have hstable : (prefixWord ++ tailWord_1749543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749543).length < 2 ^ (prefixWord ++ tailWord_1749543).sum := by decide
  have hdescent : baseEnd_1749543 < baseStart_1749543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749554 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1749554 : Nat := 118140960795 + 1749554 * 2 ^ 59
def prefixEnd_1749554 : Nat := 4983230072969 + 3 ^ 40 * 1749554 * 2
def baseEnd_1749554 : Nat := 598908088664235397085969

theorem tailTrace_1749554 : CollatzResearch.WordTrace tailWord_1749554 prefixEnd_1749554 598908088664235397085969 := by
  unfold tailWord_1749554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952869175918033219905929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42540984469114755253082477 15952869175918033219905929)
  ·
    refine ⟨11964651881938524914929447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15952869175918033219905929 11964651881938524914929447)
    ·
      refine ⟨17946977822907787372394171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11964651881938524914929447 17946977822907787372394171)
      ·
        refine ⟨26920466734361681058591257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946977822907787372394171 26920466734361681058591257)
        ·
          refine ⟨20190350050771260793943443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26920466734361681058591257 20190350050771260793943443)
          ·
            refine ⟨30285525076156891190915165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20190350050771260793943443 30285525076156891190915165)
            ·
              refine ⟨11357071903558834196593187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30285525076156891190915165 11357071903558834196593187)
              ·
                refine ⟨17035607855338251294889781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11357071903558834196593187 17035607855338251294889781)
                ·
                  refine ⟨1597088236437961058895917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17035607855338251294889781 1597088236437961058895917)
                  ·
                    refine ⟨598908088664235397085969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597088236437961058895917 598908088664235397085969)
                    ·
                      rfl

theorem cell22_1749554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1749554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749554 prefixEnd_1749554 := by exact prefixLift 1749554
  have htrace : WordTrace (prefixWord ++ tailWord_1749554) baseStart_1749554 baseEnd_1749554 := by
    simpa [prefixWord, tailWord_1749554, baseEnd_1749554] using wordTrace_append hprefix tailTrace_1749554
  have hstable : (prefixWord ++ tailWord_1749554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749554).length < 2 ^ (prefixWord ++ tailWord_1749554).sum := by decide
  have hdescent : baseEnd_1749554 < baseStart_1749554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749558 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1749558 : Nat := 118140960795 + 1749558 * 2 ^ 59
def prefixEnd_1749558 : Nat := 4983230072969 + 3 ^ 40 * 1749558 * 2
def baseEnd_1749558 : Nat := 598909457945980719985957

theorem tailTrace_1749558 : CollatzResearch.WordTrace tailWord_1749558 prefixEnd_1749558 598909457945980719985957 := by
  unfold tailWord_1749558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988226412228602597673083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42541081730438427708512885 3988226412228602597673083)
  ·
    refine ⟨5982339618342903896509625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3988226412228602597673083 5982339618342903896509625)
    ·
      refine ⟨4486754713757177922382219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5982339618342903896509625 4486754713757177922382219)
      ·
        refine ⟨6730132070635766883573329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486754713757177922382219 6730132070635766883573329)
        ·
          refine ⟨5047599052976825162679997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6730132070635766883573329 5047599052976825162679997)
          ·
            refine ⟨1892849644866309436004999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5047599052976825162679997 1892849644866309436004999)
            ·
              refine ⟨2839274467299464154007499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892849644866309436004999 2839274467299464154007499)
              ·
                refine ⟨4258911700949196231011249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839274467299464154007499 4258911700949196231011249)
                ·
                  refine ⟨3194183775711897173258437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258911700949196231011249 3194183775711897173258437)
                  ·
                    refine ⟨598909457945980719985957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194183775711897173258437 598909457945980719985957)
                    ·
                      rfl

theorem cell22_1749558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1749558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749558 prefixEnd_1749558 := by exact prefixLift 1749558
  have htrace : WordTrace (prefixWord ++ tailWord_1749558) baseStart_1749558 baseEnd_1749558 := by
    simpa [prefixWord, tailWord_1749558, baseEnd_1749558] using wordTrace_append hprefix tailTrace_1749558
  have hstable : (prefixWord ++ tailWord_1749558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749558).length < 2 ^ (prefixWord ++ tailWord_1749558).sum := by decide
  have hdescent : baseEnd_1749558 < baseStart_1749558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749567 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 7]
def baseStart_1749567 : Nat := 118140960795 + 1749567 * 2 ^ 59
def prefixEnd_1749567 : Nat := 4983230072969 + 3 ^ 40 * 1749567 * 2
def baseEnd_1749567 : Nat := 199637512943302565503643

theorem tailTrace_1749567 : CollatzResearch.WordTrace tailWord_1749567 prefixEnd_1749567 199637512943302565503643 := by
  unfold tailWord_1749567
  simp only [CollatzResearch.WordTrace]
  refine ⟨63811950852625036099846955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42541300568416690733231303 63811950852625036099846955)
  ·
    refine ⟨95717926278937554149770433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63811950852625036099846955 95717926278937554149770433)
    ·
      refine ⟨71788444709203165612327825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95717926278937554149770433 71788444709203165612327825)
      ·
        refine ⟨53841333531902374209245869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71788444709203165612327825 53841333531902374209245869)
        ·
          refine ⟨20190500074463390328467201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53841333531902374209245869 20190500074463390328467201)
          ·
            refine ⟨15142875055847542746350401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20190500074463390328467201 15142875055847542746350401)
            ·
              refine ⟨11357156291885657059762801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15142875055847542746350401 11357156291885657059762801)
              ·
                refine ⟨8517867218914242794822101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11357156291885657059762801 8517867218914242794822101)
                ·
                  refine ⟨199637512943302565503643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8517867218914242794822101 199637512943302565503643)
                  ·
                    rfl

theorem cell22_1749567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_1749567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749567 prefixEnd_1749567 := by exact prefixLift 1749567
  have htrace : WordTrace (prefixWord ++ tailWord_1749567) baseStart_1749567 baseEnd_1749567 := by
    simpa [prefixWord, tailWord_1749567, baseEnd_1749567] using wordTrace_append hprefix tailTrace_1749567
  have hstable : (prefixWord ++ tailWord_1749567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749567).length < 2 ^ (prefixWord ++ tailWord_1749567).sum := by decide
  have hdescent : baseEnd_1749567 < baseStart_1749567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749588 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_1749588 : Nat := 118140960795 + 1749588 * 2 ^ 59
def prefixEnd_1749588 : Nat := 4983230072969 + 3 ^ 40 * 1749588 * 2
def baseEnd_1749588 : Nat := 598919727559070641735865

theorem tailTrace_1749588 : CollatzResearch.WordTrace tailWord_1749588 prefixEnd_1749588 598919727559070641735865 := by
  unfold tailWord_1749588
  simp only [CollatzResearch.WordTrace]
  refine ⟨31906358392774478343180709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42541811190365971124240945 31906358392774478343180709)
  ·
    refine ⟨5982442198645214689346383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31906358392774478343180709 5982442198645214689346383)
    ·
      refine ⟨8973663297967822034019575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5982442198645214689346383 8973663297967822034019575)
      ·
        refine ⟨13460494946951733051029363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973663297967822034019575 13460494946951733051029363)
        ·
          refine ⟨20190742420427599576544045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13460494946951733051029363 20190742420427599576544045)
          ·
            refine ⟨7571528407660349841204017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20190742420427599576544045 7571528407660349841204017)
            ·
              refine ⟨5678646305745262380903013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571528407660349841204017 5678646305745262380903013)
              ·
                refine ⟨1064746182327236696419315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5678646305745262380903013 1064746182327236696419315)
                ·
                  refine ⟨1597119273490855044628973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064746182327236696419315 1597119273490855044628973)
                  ·
                    refine ⟨598919727559070641735865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597119273490855044628973 598919727559070641735865)
                    ·
                      rfl

theorem cell22_1749588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_1749588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749588 prefixEnd_1749588 := by exact prefixLift 1749588
  have htrace : WordTrace (prefixWord ++ tailWord_1749588) baseStart_1749588 baseEnd_1749588 := by
    simpa [prefixWord, tailWord_1749588, baseEnd_1749588] using wordTrace_append hprefix tailTrace_1749588
  have hstable : (prefixWord ++ tailWord_1749588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749588).length < 2 ^ (prefixWord ++ tailWord_1749588).sum := by decide
  have hdescent : baseEnd_1749588 < baseStart_1749588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749601 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 5]
def baseStart_1749601 : Nat := 118140960795 + 1749601 * 2 ^ 59
def prefixEnd_1749601 : Nat := 4983230072969 + 3 ^ 40 * 1749601 * 2
def baseEnd_1749601 : Nat := 199641392574914313720275

theorem tailTrace_1749601 : CollatzResearch.WordTrace tailWord_1749601 prefixEnd_1749601 199641392574914313720275 := by
  unfold tailWord_1749601
  simp only [CollatzResearch.WordTrace]
  refine ⟨63813190934501859906584657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42542127289667906604389771 63813190934501859906584657)
  ·
    refine ⟨47859893200876394929938493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63813190934501859906584657 47859893200876394929938493)
    ·
      refine ⟨17947459950328648098726935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47859893200876394929938493 17947459950328648098726935)
      ·
        refine ⟨26921189925492972148090403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17947459950328648098726935 26921189925492972148090403)
        ·
          refine ⟨40381784888239458222135605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26921189925492972148090403 40381784888239458222135605)
          ·
            refine ⟨3785792333272449208325213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40381784888239458222135605 3785792333272449208325213)
            ·
              refine ⟨1419672124977168453121955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3785792333272449208325213 1419672124977168453121955)
              ·
                refine ⟨2129508187465752679682933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419672124977168453121955 2129508187465752679682933)
                ·
                  refine ⟨199641392574914313720275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2129508187465752679682933 199641392574914313720275)
                  ·
                    rfl

theorem cell22_1749601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_1749601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749601 prefixEnd_1749601 := by exact prefixLift 1749601
  have htrace : WordTrace (prefixWord ++ tailWord_1749601) baseStart_1749601 baseEnd_1749601 := by
    simpa [prefixWord, tailWord_1749601, baseEnd_1749601] using wordTrace_append hprefix tailTrace_1749601
  have hstable : (prefixWord ++ tailWord_1749601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749601).length < 2 ^ (prefixWord ++ tailWord_1749601).sum := by decide
  have hdescent : baseEnd_1749601 < baseStart_1749601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749622 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1749622 : Nat := 118140960795 + 1749622 * 2 ^ 59
def prefixEnd_1749622 : Nat := 4983230072969 + 3 ^ 40 * 1749622 * 2
def baseEnd_1749622 : Nat := 598931366453905886385761

theorem tailTrace_1749622 : CollatzResearch.WordTrace tailWord_1749622 prefixEnd_1749622 598931366453905886385761 := by
  unfold tailWord_1749622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988372304214111280818695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42542637911617186995399413 3988372304214111280818695)
  ·
    refine ⟨5982558456321166921228043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3988372304214111280818695 5982558456321166921228043)
    ·
      refine ⟨8973837684481750381842065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5982558456321166921228043 8973837684481750381842065)
      ·
        refine ⟨6730378263361312786381549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8973837684481750381842065 6730378263361312786381549)
        ·
          refine ⟨2523891848760492294893081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6730378263361312786381549 2523891848760492294893081)
          ·
            refine ⟨1892918886570369221169811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523891848760492294893081 1892918886570369221169811)
            ·
              refine ⟨2839378329855553831754717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892918886570369221169811 2839378329855553831754717)
              ·
                refine ⟨1064766873695832686908019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2839378329855553831754717 1064766873695832686908019)
                ·
                  refine ⟨1597150310543749030362029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064766873695832686908019 1597150310543749030362029)
                  ·
                    refine ⟨598931366453905886385761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597150310543749030362029 598931366453905886385761)
                    ·
                      rfl

theorem cell22_1749622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1749622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749622 prefixEnd_1749622 := by exact prefixLift 1749622
  have htrace : WordTrace (prefixWord ++ tailWord_1749622) baseStart_1749622 baseEnd_1749622 := by
    simpa [prefixWord, tailWord_1749622, baseEnd_1749622] using wordTrace_append hprefix tailTrace_1749622
  have hstable : (prefixWord ++ tailWord_1749622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749622).length < 2 ^ (prefixWord ++ tailWord_1749622).sum := by decide
  have hdescent : baseEnd_1749622 < baseStart_1749622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749665 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 1, 4]
def baseStart_1749665 : Nat := 118140960795 + 1749665 * 2 ^ 59
def prefixEnd_1749665 : Nat := 4983230072969 + 3 ^ 40 * 1749665 * 2
def baseEnd_1749665 : Nat := 598946086232668107560629

theorem tailTrace_1749665 : CollatzResearch.WordTrace tailWord_1749665 prefixEnd_1749665 598946086232668107560629 := by
  unfold tailWord_1749665
  simp only [CollatzResearch.WordTrace]
  refine ⟨63815525206269998836914449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42543683470846665891276299 63815525206269998836914449)
  ·
    refine ⟨47861643904702499127685837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63815525206269998836914449 47861643904702499127685837)
    ·
      refine ⟨17948116464263437172882189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47861643904702499127685837 17948116464263437172882189)
      ·
        refine ⟨6730543674098788939830821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17948116464263437172882189 6730543674098788939830821)
        ·
          refine ⟨1261976938893522926218279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6730543674098788939830821 1261976938893522926218279)
          ·
            refine ⟨1892965408340284389327419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261976938893522926218279 1892965408340284389327419)
            ·
              refine ⟨2839448112510426583991129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892965408340284389327419 2839448112510426583991129)
              ·
                refine ⟨2129586084382819937993347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839448112510426583991129 2129586084382819937993347)
                ·
                  refine ⟨3194379126574229906990021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129586084382819937993347 3194379126574229906990021)
                  ·
                    refine ⟨598946086232668107560629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194379126574229906990021 598946086232668107560629)
                    ·
                      rfl

theorem cell22_1749665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_1749665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749665 prefixEnd_1749665 := by exact prefixLift 1749665
  have htrace : WordTrace (prefixWord ++ tailWord_1749665) baseStart_1749665 baseEnd_1749665 := by
    simpa [prefixWord, tailWord_1749665, baseEnd_1749665] using wordTrace_append hprefix tailTrace_1749665
  have hstable : (prefixWord ++ tailWord_1749665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749665).length < 2 ^ (prefixWord ++ tailWord_1749665).sum := by decide
  have hdescent : baseEnd_1749665 < baseStart_1749665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749678 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1749678 : Nat := 118140960795 + 1749678 * 2 ^ 59
def prefixEnd_1749678 : Nat := 4983230072969 + 3 ^ 40 * 1749678 * 2
def baseEnd_1749678 : Nat := 598950536398340406985589

theorem tailTrace_1749678 : CollatzResearch.WordTrace tailWord_1749678 prefixEnd_1749678 598950536398340406985589 := by
  unfold tailWord_1749678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976999919402862757142211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42543999570148601371425125 7976999919402862757142211)
  ·
    refine ⟨11965499879104294135713317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7976999919402862757142211 11965499879104294135713317)
    ·
      refine ⟨2243531227332055150446247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11965499879104294135713317 2243531227332055150446247)
      ·
        refine ⟨3365296840998082725669371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243531227332055150446247 3365296840998082725669371)
        ·
          refine ⟨5047945261497124088504057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365296840998082725669371 5047945261497124088504057)
          ·
            refine ⟨3785958946122843066378043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047945261497124088504057 3785958946122843066378043)
            ·
              refine ⟨5678938419184264599567065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785958946122843066378043 5678938419184264599567065)
              ·
                refine ⟨4259203814388198449675299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5678938419184264599567065 4259203814388198449675299)
                ·
                  refine ⟨6388805721582297674512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259203814388198449675299 6388805721582297674512949)
                  ·
                    refine ⟨598950536398340406985589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6388805721582297674512949 598950536398340406985589)
                    ·
                      rfl

theorem cell22_1749678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1749678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749678 prefixEnd_1749678 := by exact prefixLift 1749678
  have htrace : WordTrace (prefixWord ++ tailWord_1749678) baseStart_1749678 baseEnd_1749678 := by
    simpa [prefixWord, tailWord_1749678, baseEnd_1749678] using wordTrace_append hprefix tailTrace_1749678
  have hstable : (prefixWord ++ tailWord_1749678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749678).length < 2 ^ (prefixWord ++ tailWord_1749678).sum := by decide
  have hdescent : baseEnd_1749678 < baseStart_1749678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749704 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1749704 : Nat := 118140960795 + 1749704 * 2 ^ 59
def prefixEnd_1749704 : Nat := 4983230072969 + 3 ^ 40 * 1749704 * 2
def baseEnd_1749704 : Nat := 598959436729685005835509

theorem tailTrace_1749704 : CollatzResearch.WordTrace tailWord_1749704 prefixEnd_1749704 598959436729685005835509 := by
  unfold tailWord_1749704
  simp only [CollatzResearch.WordTrace]
  refine ⟨31908473826564354248792083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42544631768752472331722777 31908473826564354248792083)
  ·
    refine ⟨47862710739846531373188125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31908473826564354248792083 47862710739846531373188125)
    ·
      refine ⟨17948516527442449264945547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47862710739846531373188125 17948516527442449264945547)
      ·
        refine ⟨26922774791163673897418321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17948516527442449264945547 26922774791163673897418321)
        ·
          refine ⟨20192081093372755423063741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26922774791163673897418321 20192081093372755423063741)
          ·
            refine ⟨7572030410014783283648903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20192081093372755423063741 7572030410014783283648903)
            ·
              refine ⟨11358045615022174925473355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572030410014783283648903 11358045615022174925473355)
              ·
                refine ⟨17037068422533262388210033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358045615022174925473355 17037068422533262388210033)
                ·
                  refine ⟨12777801316899946791157525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17037068422533262388210033 12777801316899946791157525)
                  ·
                    refine ⟨598959436729685005835509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12777801316899946791157525 598959436729685005835509)
                    ·
                      rfl

theorem cell22_1749704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1749704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749704 prefixEnd_1749704 := by exact prefixLift 1749704
  have htrace : WordTrace (prefixWord ++ tailWord_1749704) baseStart_1749704 baseEnd_1749704 := by
    simpa [prefixWord, tailWord_1749704, baseEnd_1749704] using wordTrace_append hprefix tailTrace_1749704
  have hstable : (prefixWord ++ tailWord_1749704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749704).length < 2 ^ (prefixWord ++ tailWord_1749704).sum := by decide
  have hdescent : baseEnd_1749704 < baseStart_1749704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749811 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_1749811 : Nat := 118140960795 + 1749811 * 2 ^ 59
def prefixEnd_1749811 : Nat := 4983230072969 + 3 ^ 40 * 1749811 * 2
def baseEnd_1749811 : Nat := 598996065016372393410181

theorem tailTrace_1749811 : CollatzResearch.WordTrace tailWord_1749811 prefixEnd_1749811 598996065016372393410181 := by
  unfold tailWord_1749811
  simp only [CollatzResearch.WordTrace]
  refine ⟨63820850263741065771729287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42547233509160710514486191 63820850263741065771729287)
  ·
    refine ⟨95731275395611598657593931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63820850263741065771729287 95731275395611598657593931)
    ·
      refine ⟨143596913093417397986390897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95731275395611598657593931 143596913093417397986390897)
      ·
        refine ⟨107697684820063048489793173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143596913093417397986390897 107697684820063048489793173)
        ·
          refine ⟨5048328975940455397959055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107697684820063048489793173 5048328975940455397959055)
          ·
            refine ⟨7572493463910683096938583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048328975940455397959055 7572493463910683096938583)
            ·
              refine ⟨11358740195866024645407875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572493463910683096938583 11358740195866024645407875)
              ·
                refine ⟨17038110293799036968111813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358740195866024645407875 17038110293799036968111813)
                ·
                  refine ⟨3194645680087319431520965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17038110293799036968111813 3194645680087319431520965)
                  ·
                    refine ⟨598996065016372393410181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194645680087319431520965 598996065016372393410181)
                    ·
                      rfl

theorem cell22_1749811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_1749811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749811 prefixEnd_1749811 := by exact prefixLift 1749811
  have htrace : WordTrace (prefixWord ++ tailWord_1749811) baseStart_1749811 baseEnd_1749811 := by
    simpa [prefixWord, tailWord_1749811, baseEnd_1749811] using wordTrace_append hprefix tailTrace_1749811
  have hstable : (prefixWord ++ tailWord_1749811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749811).length < 2 ^ (prefixWord ++ tailWord_1749811).sum := by decide
  have hdescent : baseEnd_1749811 < baseStart_1749811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749813 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1749813 : Nat := 118140960795 + 1749813 * 2 ^ 59
def prefixEnd_1749813 : Nat := 4983230072969 + 3 ^ 40 * 1749813 * 2
def baseEnd_1749813 : Nat := 598996749657245054860175

theorem tailTrace_1749813 : CollatzResearch.WordTrace tailWord_1749813 prefixEnd_1749813 598996749657245054860175 := by
  unfold tailWord_1749813
  simp only [CollatzResearch.WordTrace]
  refine ⟨63820923209733820113302093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42547282139822546742201395 63820923209733820113302093)
  ·
    refine ⟨23932846203650182542488285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63820923209733820113302093 23932846203650182542488285)
    ·
      refine ⟨8974817326368818453433107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23932846203650182542488285 8974817326368818453433107)
      ·
        refine ⟨13462225989553227680149661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8974817326368818453433107 13462225989553227680149661)
        ·
          refine ⟨5048334746082460380056123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13462225989553227680149661 5048334746082460380056123)
          ·
            refine ⟨7572502119123690570084185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048334746082460380056123 7572502119123690570084185)
            ·
              refine ⟨5679376589342767927563139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7572502119123690570084185 5679376589342767927563139)
              ·
                refine ⟨8519064884014151891344709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679376589342767927563139 8519064884014151891344709)
                ·
                  refine ⟨1597324665752653479627133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8519064884014151891344709 1597324665752653479627133)
                  ·
                    refine ⟨598996749657245054860175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597324665752653479627133 598996749657245054860175)
                    ·
                      rfl

theorem cell22_1749813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1749813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749813 prefixEnd_1749813 := by exact prefixLift 1749813
  have htrace : WordTrace (prefixWord ++ tailWord_1749813) baseStart_1749813 baseEnd_1749813 := by
    simpa [prefixWord, tailWord_1749813, baseEnd_1749813] using wordTrace_append hprefix tailTrace_1749813
  have hstable : (prefixWord ++ tailWord_1749813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749813).length < 2 ^ (prefixWord ++ tailWord_1749813).sum := by decide
  have hdescent : baseEnd_1749813 < baseStart_1749813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749946 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1749946 : Nat := 118140960795 + 1749946 * 2 ^ 59
def prefixEnd_1749946 : Nat := 4983230072969 + 3 ^ 40 * 1749946 * 2
def baseEnd_1749946 : Nat := 599042278275277041284767

theorem tailTrace_1749946 : CollatzResearch.WordTrace tailWord_1749946 prefixEnd_1749946 599042278275277041284767 := by
  unfold tailWord_1749946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956443529562995956973423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42550516078834655885262461 15956443529562995956973423)
  ·
    refine ⟨23934665294344493935460135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956443529562995956973423 23934665294344493935460135)
    ·
      refine ⟨35901997941516740903190203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23934665294344493935460135 35901997941516740903190203)
      ·
        refine ⟨53852996912275111354785305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35901997941516740903190203 53852996912275111354785305)
        ·
          refine ⟨40389747684206333516088979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53852996912275111354785305 40389747684206333516088979)
          ·
            refine ⟨60584621526309500274133469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40389747684206333516088979 60584621526309500274133469)
            ·
              refine ⟨22719233072366062602800051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60584621526309500274133469 22719233072366062602800051)
              ·
                refine ⟨34078849608549093904200077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22719233072366062602800051 34078849608549093904200077)
                ·
                  refine ⟨12779568603205910214075029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34078849608549093904200077 12779568603205910214075029)
                  ·
                    refine ⟨599042278275277041284767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12779568603205910214075029 599042278275277041284767)
                    ·
                      rfl

theorem cell22_1749946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1749946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749946 prefixEnd_1749946 := by exact prefixLift 1749946
  have htrace : WordTrace (prefixWord ++ tailWord_1749946) baseStart_1749946 baseEnd_1749946 := by
    simpa [prefixWord, tailWord_1749946, baseEnd_1749946] using wordTrace_append hprefix tailTrace_1749946
  have hstable : (prefixWord ++ tailWord_1749946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749946).length < 2 ^ (prefixWord ++ tailWord_1749946).sum := by decide
  have hdescent : baseEnd_1749946 < baseStart_1749946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749978 : List Nat := [3, 1, 1, 2, 4, 3, 8]
def baseStart_1749978 : Nat := 118140960795 + 1749978 * 2 ^ 59
def prefixEnd_1749978 : Nat := 4983230072969 + 3 ^ 40 * 1749978 * 2
def baseEnd_1749978 : Nat := 22187156760342208314247

theorem tailTrace_1749978 : CollatzResearch.WordTrace tailWord_1749978 prefixEnd_1749978 22187156760342208314247 := by
  unfold tailWord_1749978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956735313534013323264647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42551294169424035528705725 15956735313534013323264647)
  ·
    refine ⟨23935102970301019984896971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956735313534013323264647 23935102970301019984896971)
    ·
      refine ⟨35902654455451529977345457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23935102970301019984896971 35902654455451529977345457)
      ·
        refine ⟨26926990841588647483009093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35902654455451529977345457 26926990841588647483009093)
        ·
          refine ⟨5048810782797871403064205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26926990841588647483009093 5048810782797871403064205)
          ·
            refine ⟨1893304043549201776149077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5048810782797871403064205 1893304043549201776149077)
            ·
              refine ⟨22187156760342208314247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1893304043549201776149077 22187156760342208314247)
              ·
                rfl

theorem cell22_1749978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 8].length) (baseStart_1749978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1749978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1749978 prefixEnd_1749978 := by exact prefixLift 1749978
  have htrace : WordTrace (prefixWord ++ tailWord_1749978) baseStart_1749978 baseEnd_1749978 := by
    simpa [prefixWord, tailWord_1749978, baseEnd_1749978] using wordTrace_append hprefix tailTrace_1749978
  have hstable : (prefixWord ++ tailWord_1749978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749978).length < 2 ^ (prefixWord ++ tailWord_1749978).sum := by decide
  have hdescent : baseEnd_1749978 < baseStart_1749978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750040 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 5]
def baseStart_1750040 : Nat := 118140960795 + 1750040 * 2 ^ 59
def prefixEnd_1750040 : Nat := 4983230072969 + 3 ^ 40 * 1750040 * 2
def baseEnd_1750040 : Nat := 199691485465430709811493

theorem tailTrace_1750040 : CollatzResearch.WordTrace tailWord_1750040 prefixEnd_1750040 199691485465430709811493 := by
  unfold tailWord_1750040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914601289955718940907787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42552801719940958587877049 31914601289955718940907787)
  ·
    refine ⟨47871901934933578411361681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31914601289955718940907787 47871901934933578411361681)
    ·
      refine ⟨35903926451200183808521261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47871901934933578411361681 35903926451200183808521261)
      ·
        refine ⟨13463972419200068928195473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35903926451200183808521261 13463972419200068928195473)
        ·
          refine ⟨10097979314400051696146605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13463972419200068928195473 10097979314400051696146605)
          ·
            refine ⟨3786742242900019386054977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10097979314400051696146605 3786742242900019386054977)
            ·
              refine ⟨2840056682175014539541233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786742242900019386054977 2840056682175014539541233)
              ·
                refine ⟨2130042511631260904655925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840056682175014539541233 2130042511631260904655925)
                ·
                  refine ⟨199691485465430709811493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130042511631260904655925 199691485465430709811493)
                  ·
                    rfl

theorem cell22_1750040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_1750040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750040 prefixEnd_1750040 := by exact prefixLift 1750040
  have htrace : WordTrace (prefixWord ++ tailWord_1750040) baseStart_1750040 baseEnd_1750040 := by
    simpa [prefixWord, tailWord_1750040, baseEnd_1750040] using wordTrace_append hprefix tailTrace_1750040
  have hstable : (prefixWord ++ tailWord_1750040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750040).length < 2 ^ (prefixWord ++ tailWord_1750040).sum := by decide
  have hdescent : baseEnd_1750040 < baseStart_1750040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750044 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1750044 : Nat := 118140960795 + 1750044 * 2 ^ 59
def prefixEnd_1750044 : Nat := 4983230072969 + 3 ^ 40 * 1750044 * 2
def baseEnd_1750044 : Nat := 599075825678037452334467

theorem tailTrace_1750044 : CollatzResearch.WordTrace tailWord_1750044 prefixEnd_1750044 599075825678037452334467 := by
  unfold tailWord_1750044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914674235948473282480593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42552898981264631043307457 31914674235948473282480593)
  ·
    refine ⟨23936005676961354961860445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31914674235948473282480593 23936005676961354961860445)
    ·
      refine ⟨8976002128860508110697667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23936005676961354961860445 8976002128860508110697667)
      ·
        refine ⟨13464003193290762166046501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976002128860508110697667 13464003193290762166046501)
        ·
          refine ⟨2524500598742017906133719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13464003193290762166046501 2524500598742017906133719)
          ·
            refine ⟨3786750898113026859200579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524500598742017906133719 3786750898113026859200579)
            ·
              refine ⟨5680126347169540288800869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786750898113026859200579 5680126347169540288800869)
              ·
                refine ⟨1065023690094288804150163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5680126347169540288800869 1065023690094288804150163)
                ·
                  refine ⟨1597535535141433206225245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065023690094288804150163 1597535535141433206225245)
                  ·
                    refine ⟨599075825678037452334467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597535535141433206225245 599075825678037452334467)
                    ·
                      rfl

theorem cell22_1750044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1750044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750044 prefixEnd_1750044 := by exact prefixLift 1750044
  have htrace : WordTrace (prefixWord ++ tailWord_1750044) baseStart_1750044 baseEnd_1750044 := by
    simpa [prefixWord, tailWord_1750044, baseEnd_1750044] using wordTrace_append hprefix tailTrace_1750044
  have hstable : (prefixWord ++ tailWord_1750044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750044).length < 2 ^ (prefixWord ++ tailWord_1750044).sum := by decide
  have hdescent : baseEnd_1750044 < baseStart_1750044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750053 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_1750053 : Nat := 118140960795 + 1750053 * 2 ^ 59
def prefixEnd_1750053 : Nat := 4983230072969 + 3 ^ 40 * 1750053 * 2
def baseEnd_1750053 : Nat := 599078906561964428859439

theorem tailTrace_1750053 : CollatzResearch.WordTrace tailWord_1750053 prefixEnd_1750053 599078906561964428859439 := by
  unfold tailWord_1750053
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829676728864341102038813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553117819242894068025875 63829676728864341102038813)
  ·
    refine ⟨23936128773324127913264555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63829676728864341102038813 23936128773324127913264555)
    ·
      refine ⟨35904193159986191869896833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23936128773324127913264555 35904193159986191869896833)
      ·
        refine ⟨26928144869989643902422625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35904193159986191869896833 26928144869989643902422625)
        ·
          refine ⟨20196108652492232926816969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26928144869989643902422625 20196108652492232926816969)
          ·
            refine ⟨15147081489369174695112727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20196108652492232926816969 15147081489369174695112727)
            ·
              refine ⟨22720622234053762042669091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15147081489369174695112727 22720622234053762042669091)
              ·
                refine ⟨34080933351080643064003637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22720622234053762042669091 34080933351080643064003637)
                ·
                  refine ⟨3195087501663810287250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34080933351080643064003637 3195087501663810287250341)
                  ·
                    refine ⟨599078906561964428859439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3195087501663810287250341 599078906561964428859439)
                    ·
                      rfl

theorem cell22_1750053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_1750053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750053 prefixEnd_1750053 := by exact prefixLift 1750053
  have htrace : WordTrace (prefixWord ++ tailWord_1750053) baseStart_1750053 baseEnd_1750053 := by
    simpa [prefixWord, tailWord_1750053, baseEnd_1750053] using wordTrace_append hprefix tailTrace_1750053
  have hstable : (prefixWord ++ tailWord_1750053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750053).length < 2 ^ (prefixWord ++ tailWord_1750053).sum := by decide
  have hdescent : baseEnd_1750053 < baseStart_1750053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750055 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1750055 : Nat := 118140960795 + 1750055 * 2 ^ 59
def prefixEnd_1750055 : Nat := 4983230072969 + 3 ^ 40 * 1750055 * 2
def baseEnd_1750055 : Nat := 599079591202837090309433

theorem tailTrace_1750055 : CollatzResearch.WordTrace tailWord_1750055 prefixEnd_1750055 599079591202837090309433 := by
  unfold tailWord_1750055
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829749674857095443611619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553166449904730295741079 63829749674857095443611619)
  ·
    refine ⟨95744624512285643165417429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63829749674857095443611619 95744624512285643165417429)
    ·
      refine ⟨2244014637006694761689471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95744624512285643165417429 2244014637006694761689471)
      ·
        refine ⟨3366021955510042142534207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244014637006694761689471 3366021955510042142534207)
        ·
          refine ⟨5049032933265063213801311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366021955510042142534207 5049032933265063213801311)
          ·
            refine ⟨7573549399897594820701967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049032933265063213801311 7573549399897594820701967)
            ·
              refine ⟨11360324099846392231052951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573549399897594820701967 11360324099846392231052951)
              ·
                refine ⟨17040486149769588346579427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11360324099846392231052951 17040486149769588346579427)
                ·
                  refine ⟨25560729224654382519869141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17040486149769588346579427 25560729224654382519869141)
                  ·
                    refine ⟨599079591202837090309433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25560729224654382519869141 599079591202837090309433)
                    ·
                      rfl

theorem cell22_1750055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1750055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750055 prefixEnd_1750055 := by exact prefixLift 1750055
  have htrace : WordTrace (prefixWord ++ tailWord_1750055) baseStart_1750055 baseEnd_1750055 := by
    simpa [prefixWord, tailWord_1750055, baseEnd_1750055] using wordTrace_append hprefix tailTrace_1750055
  have hstable : (prefixWord ++ tailWord_1750055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750055).length < 2 ^ (prefixWord ++ tailWord_1750055).sum := by decide
  have hdescent : baseEnd_1750055 < baseStart_1750055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750083 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_1750083 : Nat := 118140960795 + 1750083 * 2 ^ 59
def prefixEnd_1750083 : Nat := 4983230072969 + 3 ^ 40 * 1750083 * 2
def baseEnd_1750083 : Nat := 599089176175054350609347

theorem tailTrace_1750083 : CollatzResearch.WordTrace tailWord_1750083 prefixEnd_1750083 599089176175054350609347 := by
  unfold tailWord_1750083
  simp only [CollatzResearch.WordTrace]
  refine ⟨63830770918755656225630903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553847279170437483753935 63830770918755656225630903)
  ·
    refine ⟨95746156378133484338446355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63830770918755656225630903 95746156378133484338446355)
    ·
      refine ⟨143619234567200226507669533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95746156378133484338446355 143619234567200226507669533)
      ·
        refine ⟨53857212962700084940376075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143619234567200226507669533 53857212962700084940376075)
        ·
          refine ⟨80785819444050127410564113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53857212962700084940376075 80785819444050127410564113)
          ·
            refine ⟨60589364583037595557923085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80785819444050127410564113 60589364583037595557923085)
            ·
              refine ⟨22721011718639098334221157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60589364583037595557923085 22721011718639098334221157)
              ·
                refine ⟨4260189697244830937666467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22721011718639098334221157 4260189697244830937666467)
                ·
                  refine ⟨6390284545867246406499701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260189697244830937666467 6390284545867246406499701)
                  ·
                    refine ⟨599089176175054350609347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6390284545867246406499701 599089176175054350609347)
                    ·
                      rfl

theorem cell22_1750083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_1750083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750083 prefixEnd_1750083 := by exact prefixLift 1750083
  have htrace : WordTrace (prefixWord ++ tailWord_1750083) baseStart_1750083 baseEnd_1750083 := by
    simpa [prefixWord, tailWord_1750083, baseEnd_1750083] using wordTrace_append hprefix tailTrace_1750083
  have hstable : (prefixWord ++ tailWord_1750083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750083).length < 2 ^ (prefixWord ++ tailWord_1750083).sum := by decide
  have hdescent : baseEnd_1750083 < baseStart_1750083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750085 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 4]
def baseStart_1750085 : Nat := 118140960795 + 1750085 * 2 ^ 59
def prefixEnd_1750085 : Nat := 4983230072969 + 3 ^ 40 * 1750085 * 2
def baseEnd_1750085 : Nat := 199696620271975670686447

theorem tailTrace_1750085 : CollatzResearch.WordTrace tailWord_1750085 prefixEnd_1750085 199696620271975670686447 := by
  unfold tailWord_1750085
  simp only [CollatzResearch.WordTrace]
  refine ⟨63830843864748410567203709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553895909832273711469139 63830843864748410567203709)
  ·
    refine ⟨23936566449280653962701391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63830843864748410567203709 23936566449280653962701391)
    ·
      refine ⟨35904849673920980944052087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23936566449280653962701391 35904849673920980944052087)
      ·
        refine ⟨53857274510881471416078131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35904849673920980944052087 53857274510881471416078131)
        ·
          refine ⟨80785911766322207124117197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53857274510881471416078131 80785911766322207124117197)
          ·
            refine ⟨30294716912370827671543949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80785911766322207124117197 30294716912370827671543949)
            ·
              refine ⟨11360518842139060376828981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30294716912370827671543949 11360518842139060376828981)
              ·
                refine ⟨1065048641450536910327717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11360518842139060376828981 1065048641450536910327717)
                ·
                  refine ⟨199696620271975670686447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065048641450536910327717 199696620271975670686447)
                  ·
                    rfl

theorem cell22_1750085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_1750085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750085 prefixEnd_1750085 := by exact prefixLift 1750085
  have htrace : WordTrace (prefixWord ++ tailWord_1750085) baseStart_1750085 baseEnd_1750085 := by
    simpa [prefixWord, tailWord_1750085, baseEnd_1750085] using wordTrace_append hprefix tailTrace_1750085
  have hstable : (prefixWord ++ tailWord_1750085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750085).length < 2 ^ (prefixWord ++ tailWord_1750085).sum := by decide
  have hdescent : baseEnd_1750085 < baseStart_1750085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750087 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1750087 : Nat := 118140960795 + 1750087 * 2 ^ 59
def prefixEnd_1750087 : Nat := 4983230072969 + 3 ^ 40 * 1750087 * 2
def baseEnd_1750087 : Nat := 599090545456799673509335

theorem tailTrace_1750087 : CollatzResearch.WordTrace tailWord_1750087 prefixEnd_1750087 599090545456799673509335 := by
  unfold tailWord_1750087
  simp only [CollatzResearch.WordTrace]
  refine ⟨63830916810741164908776515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553944540494109939184343 63830916810741164908776515)
  ·
    refine ⟨95746375216111747363164773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63830916810741164908776515 95746375216111747363164773)
    ·
      refine ⟨17952445353020952630593395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95746375216111747363164773 17952445353020952630593395)
      ·
        refine ⟨26928668029531428945890093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17952445353020952630593395 26928668029531428945890093)
        ·
          refine ⟨10098250511074285854708785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26928668029531428945890093 10098250511074285854708785)
          ·
            refine ⟨7573687883305714391031589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10098250511074285854708785 7573687883305714391031589)
            ·
              refine ⟨1420066478119821448318423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7573687883305714391031589 1420066478119821448318423)
              ·
                refine ⟨2130099717179732172477635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420066478119821448318423 2130099717179732172477635)
                ·
                  refine ⟨3195149575769598258716453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130099717179732172477635 3195149575769598258716453)
                  ·
                    refine ⟨599090545456799673509335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3195149575769598258716453 599090545456799673509335)
                    ·
                      rfl

theorem cell22_1750087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1750087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750087 prefixEnd_1750087 := by exact prefixLift 1750087
  have htrace : WordTrace (prefixWord ++ tailWord_1750087) baseStart_1750087 baseEnd_1750087 := by
    simpa [prefixWord, tailWord_1750087, baseEnd_1750087] using wordTrace_append hprefix tailTrace_1750087
  have hstable : (prefixWord ++ tailWord_1750087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750087).length < 2 ^ (prefixWord ++ tailWord_1750087).sum := by decide
  have hdescent : baseEnd_1750087 < baseStart_1750087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750128 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_1750128 : Nat := 118140960795 + 1750128 * 2 ^ 59
def prefixEnd_1750128 : Nat := 4983230072969 + 3 ^ 40 * 1750128 * 2
def baseEnd_1750128 : Nat := 599104580594689233234209

theorem tailTrace_1750128 : CollatzResearch.WordTrace tailWord_1750128 prefixEnd_1750128 599104580594689233234209 := by
  unfold tailWord_1750128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31916206101796314455509519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42554941469061752607346025 31916206101796314455509519)
  ·
    refine ⟨47874309152694471683264279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31916206101796314455509519 47874309152694471683264279)
    ·
      refine ⟨71811463729041707524896419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47874309152694471683264279 71811463729041707524896419)
      ·
        refine ⟨107717195593562561287344629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71811463729041707524896419 107717195593562561287344629)
        ·
          refine ⟨10098487086896490120688559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107717195593562561287344629 10098487086896490120688559)
          ·
            refine ⟨15147730630344735181032839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10098487086896490120688559 15147730630344735181032839)
            ·
              refine ⟨22721595945517102771549259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15147730630344735181032839 22721595945517102771549259)
              ·
                refine ⟨34082393918275654157323889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22721595945517102771549259 34082393918275654157323889)
                ·
                  refine ⟨25561795438706740617992917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34082393918275654157323889 25561795438706740617992917)
                  ·
                    refine ⟨599104580594689233234209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25561795438706740617992917 599104580594689233234209)
                    ·
                      rfl

theorem cell22_1750128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_1750128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750128 prefixEnd_1750128 := by exact prefixLift 1750128
  have htrace : WordTrace (prefixWord ++ tailWord_1750128) baseStart_1750128 baseEnd_1750128 := by
    simpa [prefixWord, tailWord_1750128, baseEnd_1750128] using wordTrace_append hprefix tailTrace_1750128
  have hstable : (prefixWord ++ tailWord_1750128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750128).length < 2 ^ (prefixWord ++ tailWord_1750128).sum := by decide
  have hdescent : baseEnd_1750128 < baseStart_1750128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750203 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 10]
def baseStart_1750203 : Nat := 118140960795 + 1750203 * 2 ^ 59
def prefixEnd_1750203 : Nat := 4983230072969 + 3 ^ 40 * 1750203 * 2
def baseEnd_1750203 : Nat := 199710084875804679202993

theorem tailTrace_1750203 : CollatzResearch.WordTrace tailWord_1750203 prefixEnd_1750203 199710084875804679202993 := by
  unfold tailWord_1750203
  simp only [CollatzResearch.WordTrace]
  refine ⟨63835147678320916719999263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42556765118880611146666175 63835147678320916719999263)
  ·
    refine ⟨95752721517481375079998895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63835147678320916719999263 95752721517481375079998895)
    ·
      refine ⟨143629082276222062619998343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95752721517481375079998895 143629082276222062619998343)
      ·
        refine ⟨215443623414333093929997515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143629082276222062619998343 215443623414333093929997515)
        ·
          refine ⟨323165435121499640894996273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215443623414333093929997515 323165435121499640894996273)
          ·
            refine ⟨242374076341124730671247205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323165435121499640894996273 242374076341124730671247205)
            ·
              refine ⟨45445139313960887000858851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242374076341124730671247205 45445139313960887000858851)
              ·
                refine ⟨68167708970941330501288277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45445139313960887000858851 68167708970941330501288277)
                ·
                  refine ⟨199710084875804679202993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 68167708970941330501288277 199710084875804679202993)
                  ·
                    rfl

theorem cell22_1750203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_1750203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750203 prefixEnd_1750203 := by exact prefixLift 1750203
  have htrace : WordTrace (prefixWord ++ tailWord_1750203) baseStart_1750203 baseEnd_1750203 := by
    simpa [prefixWord, tailWord_1750203, baseEnd_1750203] using wordTrace_append hprefix tailTrace_1750203
  have hstable : (prefixWord ++ tailWord_1750203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750203).length < 2 ^ (prefixWord ++ tailWord_1750203).sum := by decide
  have hdescent : baseEnd_1750203 < baseStart_1750203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750209 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 5]
def baseStart_1750209 : Nat := 118140960795 + 1750209 * 2 ^ 59
def prefixEnd_1750209 : Nat := 4983230072969 + 3 ^ 40 * 1750209 * 2
def baseEnd_1750209 : Nat := 199710769516677340652987

theorem tailTrace_1750209 : CollatzResearch.WordTrace tailWord_1750209 prefixEnd_1750209 199710769516677340652987 := by
  unfold tailWord_1750209
  simp only [CollatzResearch.WordTrace]
  refine ⟨63835366516299179744717681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42556911010866119829811787 63835366516299179744717681)
  ·
    refine ⟨47876524887224384808538261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63835366516299179744717681 47876524887224384808538261)
    ·
      refine ⟨2244212104088643037900231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47876524887224384808538261 2244212104088643037900231)
      ·
        refine ⟨3366318156132964556850347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244212104088643037900231 3366318156132964556850347)
        ·
          refine ⟨5049477234199446835275521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366318156132964556850347 5049477234199446835275521)
          ·
            refine ⟨3787107925649585126456641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5049477234199446835275521 3787107925649585126456641)
            ·
              refine ⟨2840330944237188844842481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787107925649585126456641 2840330944237188844842481)
              ·
                refine ⟨2130248208177891633631861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840330944237188844842481 2130248208177891633631861)
                ·
                  refine ⟨199710769516677340652987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130248208177891633631861 199710769516677340652987)
                  ·
                    rfl

theorem cell22_1750209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_1750209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750209 prefixEnd_1750209 := by exact prefixLift 1750209
  have htrace : WordTrace (prefixWord ++ tailWord_1750209) baseStart_1750209 baseEnd_1750209 := by
    simpa [prefixWord, tailWord_1750209, baseEnd_1750209] using wordTrace_append hprefix tailTrace_1750209
  have hstable : (prefixWord ++ tailWord_1750209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750209).length < 2 ^ (prefixWord ++ tailWord_1750209).sum := by decide
  have hdescent : baseEnd_1750209 < baseStart_1750209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750260 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1750260 : Nat := 118140960795 + 1750260 * 2 ^ 59
def prefixEnd_1750260 : Nat := 4983230072969 + 3 ^ 40 * 1750260 * 2
def baseEnd_1750260 : Nat := 199716588964094962977935

theorem tailTrace_1750260 : CollatzResearch.WordTrace tailWord_1750260 prefixEnd_1750260 199716588964094962977935 := by
  unfold tailWord_1750260
  simp only [CollatzResearch.WordTrace]
  refine ⟨31918613319557207727412117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42558151092742943636549489 31918613319557207727412117)
  ·
    refine ⟨1496184999354244112222443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31918613319557207727412117 1496184999354244112222443)
    ·
      refine ⟨2244277499031366168333665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496184999354244112222443 2244277499031366168333665)
      ·
        refine ⟨1683208124273524626250249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2244277499031366168333665 1683208124273524626250249)
        ·
          refine ⟨1262406093205143469687687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683208124273524626250249 1262406093205143469687687)
          ·
            refine ⟨1893609139807715204531531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262406093205143469687687 1893609139807715204531531)
            ·
              refine ⟨2840413709711572806797297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893609139807715204531531 2840413709711572806797297)
              ·
                refine ⟨2130310282283679605097973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840413709711572806797297 2130310282283679605097973)
                ·
                  refine ⟨199716588964094962977935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130310282283679605097973 199716588964094962977935)
                  ·
                    rfl

theorem cell22_1750260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1750260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750260 prefixEnd_1750260 := by exact prefixLift 1750260
  have htrace : WordTrace (prefixWord ++ tailWord_1750260) baseStart_1750260 baseEnd_1750260 := by
    simpa [prefixWord, tailWord_1750260, baseEnd_1750260] using wordTrace_append hprefix tailTrace_1750260
  have hstable : (prefixWord ++ tailWord_1750260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750260).length < 2 ^ (prefixWord ++ tailWord_1750260).sum := by decide
  have hdescent : baseEnd_1750260 < baseStart_1750260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750286 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_1750286 : Nat := 118140960795 + 1750286 * 2 ^ 59
def prefixEnd_1750286 : Nat := 4983230072969 + 3 ^ 40 * 1750286 * 2
def baseEnd_1750286 : Nat := 599158667223629487783725

theorem tailTrace_1750286 : CollatzResearch.WordTrace tailWord_1750286 prefixEnd_1750286 599158667223629487783725 := by
  unfold tailWord_1750286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979771867127527736908839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42558783291346814596847141 7979771867127527736908839)
  ·
    refine ⟨11969657800691291605363259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979771867127527736908839 11969657800691291605363259)
    ·
      refine ⟨17954486701036937408044889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969657800691291605363259 17954486701036937408044889)
      ·
        refine ⟨13465865025777703056033667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17954486701036937408044889 13465865025777703056033667)
        ·
          refine ⟨20198797538666554584050501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13465865025777703056033667 20198797538666554584050501)
          ·
            refine ⟨3787274538499978984509469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20198797538666554584050501 3787274538499978984509469)
            ·
              refine ⟨1420227951937492119191051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3787274538499978984509469 1420227951937492119191051)
              ·
                refine ⟨2130341927906238178786577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420227951937492119191051 2130341927906238178786577)
                ·
                  refine ⟨1597756445929678634089933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2130341927906238178786577 1597756445929678634089933)
                  ·
                    refine ⟨599158667223629487783725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597756445929678634089933 599158667223629487783725)
                    ·
                      rfl

theorem cell22_1750286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_1750286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750286 prefixEnd_1750286 := by exact prefixLift 1750286
  have htrace : WordTrace (prefixWord ++ tailWord_1750286) baseStart_1750286 baseEnd_1750286 := by
    simpa [prefixWord, tailWord_1750286, baseEnd_1750286] using wordTrace_append hprefix tailTrace_1750286
  have hstable : (prefixWord ++ tailWord_1750286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750286).length < 2 ^ (prefixWord ++ tailWord_1750286).sum := by decide
  have hdescent : baseEnd_1750286 < baseStart_1750286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750355 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 8]
def baseStart_1750355 : Nat := 118140960795 + 1750355 * 2 ^ 59
def prefixEnd_1750355 : Nat := 4983230072969 + 3 ^ 40 * 1750355 * 2
def baseEnd_1750355 : Nat := 199727429111245435936171

theorem tailTrace_1750355 : CollatzResearch.WordTrace tailWord_1750355 prefixEnd_1750355 199727429111245435936171 := by
  unfold tailWord_1750355
  simp only [CollatzResearch.WordTrace]
  refine ⟨63840691573770246679532519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42560461049180164453021679 63840691573770246679532519)
  ·
    refine ⟨95761037360655370019298779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63840691573770246679532519 95761037360655370019298779)
    ·
      refine ⟨143641556040983055028948169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95761037360655370019298779 143641556040983055028948169)
      ·
        refine ⟨107731167030737291271711127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143641556040983055028948169 107731167030737291271711127)
        ·
          refine ⟨161596750546105936907566691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107731167030737291271711127 161596750546105936907566691)
          ·
            refine ⟨242395125819158905361350037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161596750546105936907566691 242395125819158905361350037)
            ·
              refine ⟨11362271522773073688813283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242395125819158905361350037 11362271522773073688813283)
              ·
                refine ⟨17043407284159610533219925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362271522773073688813283 17043407284159610533219925)
                ·
                  refine ⟨199727429111245435936171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17043407284159610533219925 199727429111245435936171)
                  ·
                    rfl

theorem cell22_1750355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_1750355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750355 prefixEnd_1750355 := by exact prefixLift 1750355
  have htrace : WordTrace (prefixWord ++ tailWord_1750355) baseStart_1750355 baseEnd_1750355 := by
    simpa [prefixWord, tailWord_1750355, baseEnd_1750355] using wordTrace_append hprefix tailTrace_1750355
  have hstable : (prefixWord ++ tailWord_1750355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750355).length < 2 ^ (prefixWord ++ tailWord_1750355).sum := by decide
  have hdescent : baseEnd_1750355 < baseStart_1750355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750382 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1750382 : Nat := 118140960795 + 1750382 * 2 ^ 59
def prefixEnd_1750382 : Nat := 4983230072969 + 3 ^ 40 * 1750382 * 2
def baseEnd_1750382 : Nat := 599191529985517237383431

theorem tailTrace_1750382 : CollatzResearch.WordTrace tailWord_1750382 prefixEnd_1750382 599191529985517237383431 := by
  unfold tailWord_1750382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7980209543084053786345675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42561117563114953527176933 7980209543084053786345675)
  ·
    refine ⟨11970314314626080679518513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7980209543084053786345675 11970314314626080679518513)
    ·
      refine ⟨8977735735969560509638885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11970314314626080679518513 8977735735969560509638885)
      ·
        refine ⟨1683325450494292595557291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8977735735969560509638885 1683325450494292595557291)
        ·
          refine ⟨2524988175741438893335937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683325450494292595557291 2524988175741438893335937)
          ·
            refine ⟨1893741131806079170001953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524988175741438893335937 1893741131806079170001953)
            ·
              refine ⟨1420305848854559377501465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893741131806079170001953 1420305848854559377501465)
              ·
                refine ⟨1065229386640919533126099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420305848854559377501465 1065229386640919533126099)
                ·
                  refine ⟨1597844079961379299689149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065229386640919533126099 1597844079961379299689149)
                  ·
                    refine ⟨599191529985517237383431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1597844079961379299689149 599191529985517237383431)
                    ·
                      rfl

theorem cell22_1750382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1750382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750382 prefixEnd_1750382 := by exact prefixLift 1750382
  have htrace : WordTrace (prefixWord ++ tailWord_1750382) baseStart_1750382 baseEnd_1750382 := by
    simpa [prefixWord, tailWord_1750382, baseEnd_1750382] using wordTrace_append hprefix tailTrace_1750382
  have hstable : (prefixWord ++ tailWord_1750382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750382).length < 2 ^ (prefixWord ++ tailWord_1750382).sum := by decide
  have hdescent : baseEnd_1750382 < baseStart_1750382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750404 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1750404 : Nat := 118140960795 + 1750404 * 2 ^ 59
def prefixEnd_1750404 : Nat := 4983230072969 + 3 ^ 40 * 1750404 * 2
def baseEnd_1750404 : Nat := 599199061035116513333363

theorem tailTrace_1750404 : CollatzResearch.WordTrace tailWord_1750404 prefixEnd_1750404 599199061035116513333363 := by
  unfold tailWord_1750404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31921239375296364024033133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42561652500395152032044177 31921239375296364024033133)
  ·
    refine ⟨11970464765736136509012425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31921239375296364024033133 11970464765736136509012425)
    ·
      refine ⟨8977848574302102381759319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11970464765736136509012425 8977848574302102381759319)
      ·
        refine ⟨13466772861453153572638979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8977848574302102381759319 13466772861453153572638979)
        ·
          refine ⟨20200159292179730358958469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13466772861453153572638979 20200159292179730358958469)
          ·
            refine ⟨3787529867283699442304713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20200159292179730358958469 3787529867283699442304713)
            ·
              refine ⟨2840647400462774581728535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787529867283699442304713 2840647400462774581728535)
              ·
                refine ⟨4260971100694161872592803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840647400462774581728535 4260971100694161872592803)
                ·
                  refine ⟨6391456651041242808889205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260971100694161872592803 6391456651041242808889205)
                  ·
                    refine ⟨599199061035116513333363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391456651041242808889205 599199061035116513333363)
                    ·
                      rfl

theorem cell22_1750404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1750404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750404 prefixEnd_1750404 := by exact prefixLift 1750404
  have htrace : WordTrace (prefixWord ++ tailWord_1750404) baseStart_1750404 baseEnd_1750404 := by
    simpa [prefixWord, tailWord_1750404, baseEnd_1750404] using wordTrace_append hprefix tailTrace_1750404
  have hstable : (prefixWord ++ tailWord_1750404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750404).length < 2 ^ (prefixWord ++ tailWord_1750404).sum := by decide
  have hdescent : baseEnd_1750404 < baseStart_1750404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750507 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 6]
def baseStart_1750507 : Nat := 118140960795 + 1750507 * 2 ^ 59
def prefixEnd_1750507 : Nat := 4983230072969 + 3 ^ 40 * 1750507 * 2
def baseEnd_1750507 : Nat := 199744773346686192669349

theorem tailTrace_1750507 : CollatzResearch.WordTrace tailWord_1750507 prefixEnd_1750507 199744773346686192669349 := by
  unfold tailWord_1750507
  simp only [CollatzResearch.WordTrace]
  refine ⟨63846235469219576639065775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42564156979479717759377183 63846235469219576639065775)
  ·
    refine ⟨95769353203829364958598663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63846235469219576639065775 95769353203829364958598663)
    ·
      refine ⟨143654029805744047437897995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95769353203829364958598663 143654029805744047437897995)
      ·
        refine ⟨215481044708616071156846993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143654029805744047437897995 215481044708616071156846993)
        ·
          refine ⟨161610783531462053367635245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215481044708616071156846993 161610783531462053367635245)
          ·
            refine ⟨60604043824298270012863217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161610783531462053367635245 60604043824298270012863217)
            ·
              refine ⟨45453032868223702509647413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60604043824298270012863217 45453032868223702509647413)
              ·
                refine ⟨4261221831395972110279445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45453032868223702509647413 4261221831395972110279445)
                ·
                  refine ⟨199744773346686192669349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4261221831395972110279445 199744773346686192669349)
                  ·
                    rfl

theorem cell22_1750507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_1750507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750507 prefixEnd_1750507 := by exact prefixLift 1750507
  have htrace : WordTrace (prefixWord ++ tailWord_1750507) baseStart_1750507 baseEnd_1750507 := by
    simpa [prefixWord, tailWord_1750507, baseEnd_1750507] using wordTrace_append hprefix tailTrace_1750507
  have hstable : (prefixWord ++ tailWord_1750507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750507).length < 2 ^ (prefixWord ++ tailWord_1750507).sum := by decide
  have hdescent : baseEnd_1750507 < baseStart_1750507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750552 : List Nat := [2, 1, 2, 3, 14]
def baseStart_1750552 : Nat := 118140960795 + 1750552 * 2 ^ 59
def prefixEnd_1750552 : Nat := 4983230072969 + 3 ^ 40 * 1750552 * 2
def baseEnd_1750552 : Nat := 2466048248805322883263

theorem tailTrace_1750552 : CollatzResearch.WordTrace tailWord_1750552 prefixEnd_1750552 2466048248805322883263 := by
  unfold tailWord_1750552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31923938377028274662226955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42565251169371032882969273 31923938377028274662226955)
  ·
    refine ⟨47885907565542411993340433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31923938377028274662226955 47885907565542411993340433)
    ·
      refine ⟨35914430674156808995005325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47885907565542411993340433 35914430674156808995005325)
      ·
        refine ⟨13467911502808803373126997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35914430674156808995005325 13467911502808803373126997)
        ·
          refine ⟨2466048248805322883263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 13467911502808803373126997 2466048248805322883263)
          ·
            rfl

theorem cell22_1750552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 14].length) (baseStart_1750552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750552 prefixEnd_1750552 := by exact prefixLift 1750552
  have htrace : WordTrace (prefixWord ++ tailWord_1750552) baseStart_1750552 baseEnd_1750552 := by
    simpa [prefixWord, tailWord_1750552, baseEnd_1750552] using wordTrace_append hprefix tailTrace_1750552
  have hstable : (prefixWord ++ tailWord_1750552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750552).length < 2 ^ (prefixWord ++ tailWord_1750552).sum := by decide
  have hdescent : baseEnd_1750552 < baseStart_1750552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750588 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1750588 : Nat := 118140960795 + 1750588 * 2 ^ 59
def prefixEnd_1750588 : Nat := 4983230072969 + 3 ^ 40 * 1750588 * 2
def baseEnd_1750588 : Nat := 599262047995401366732799

theorem tailTrace_1750588 : CollatzResearch.WordTrace tailWord_1750588 prefixEnd_1750588 599262047995401366732799 := by
  unfold tailWord_1750588
  simp only [CollatzResearch.WordTrace]
  refine ⟨31924594890963063736382209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42566126521284084981842945 31924594890963063736382209)
  ·
    refine ⟨23943446168222297802286657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31924594890963063736382209 23943446168222297802286657)
    ·
      refine ⟨17957584626166723351714993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23943446168222297802286657 17957584626166723351714993)
      ·
        refine ⟨13468188469625042513786245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17957584626166723351714993 13468188469625042513786245)
        ·
          refine ⟨2525285338054695471334921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13468188469625042513786245 2525285338054695471334921)
          ·
            refine ⟨1893964003541021603501191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525285338054695471334921 1893964003541021603501191)
            ·
              refine ⟨2840946005311532405251787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893964003541021603501191 2840946005311532405251787)
              ·
                refine ⟨4261419007967298607877681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840946005311532405251787 4261419007967298607877681)
                ·
                  refine ⟨3196064255975473955908261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4261419007967298607877681 3196064255975473955908261)
                  ·
                    refine ⟨599262047995401366732799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196064255975473955908261 599262047995401366732799)
                    ·
                      rfl

theorem cell22_1750588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1750588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750588 prefixEnd_1750588 := by exact prefixLift 1750588
  have htrace : WordTrace (prefixWord ++ tailWord_1750588) baseStart_1750588 baseEnd_1750588 := by
    simpa [prefixWord, tailWord_1750588, baseEnd_1750588] using wordTrace_append hprefix tailTrace_1750588
  have hstable : (prefixWord ++ tailWord_1750588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750588).length < 2 ^ (prefixWord ++ tailWord_1750588).sum := by decide
  have hdescent : baseEnd_1750588 < baseStart_1750588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750661 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_1750661 : Nat := 118140960795 + 1750661 * 2 ^ 59
def prefixEnd_1750661 : Nat := 4983230072969 + 3 ^ 40 * 1750661 * 2
def baseEnd_1750661 : Nat := 599287037387253509657575

theorem tailTrace_1750661 : CollatzResearch.WordTrace tailWord_1750661 prefixEnd_1750661 599287037387253509657575 := by
  unfold tailWord_1750661
  simp only [CollatzResearch.WordTrace]
  refine ⟨63851852310661660940171837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42567901540441107293447891 63851852310661660940171837)
  ·
    refine ⟨23944444616498122852564439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63851852310661660940171837 23944444616498122852564439)
    ·
      refine ⟨35916666924747184278846659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23944444616498122852564439 35916666924747184278846659)
      ·
        refine ⟨53875000387120776418269989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35916666924747184278846659 53875000387120776418269989)
        ·
          refine ⟨10101562572585145578425623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53875000387120776418269989 10101562572585145578425623)
          ·
            refine ⟨15152343858877718367638435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101562572585145578425623 15152343858877718367638435)
            ·
              refine ⟨22728515788316577551457653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15152343858877718367638435 22728515788316577551457653)
              ·
                refine ⟨2130798355154679145449155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22728515788316577551457653 2130798355154679145449155)
                ·
                  refine ⟨3196197532732018718173733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130798355154679145449155 3196197532732018718173733)
                  ·
                    refine ⟨599287037387253509657575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196197532732018718173733 599287037387253509657575)
                    ·
                      rfl

theorem cell22_1750661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_1750661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750661 prefixEnd_1750661 := by exact prefixLift 1750661
  have htrace : WordTrace (prefixWord ++ tailWord_1750661) baseStart_1750661 baseEnd_1750661 := by
    simpa [prefixWord, tailWord_1750661, baseEnd_1750661] using wordTrace_append hprefix tailTrace_1750661
  have hstable : (prefixWord ++ tailWord_1750661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750661).length < 2 ^ (prefixWord ++ tailWord_1750661).sum := by decide
  have hdescent : baseEnd_1750661 < baseStart_1750661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750704 : List Nat := [2, 1, 1, 1, 2, 1, 6, 8]
def baseStart_1750704 : Nat := 118140960795 + 1750704 * 2 ^ 59
def prefixEnd_1750704 : Nat := 4983230072969 + 3 ^ 40 * 1750704 * 2
def baseEnd_1750704 : Nat := 66589084129557303425827

theorem tailTrace_1750704 : CollatzResearch.WordTrace tailWord_1750704 prefixEnd_1750704 66589084129557303425827 := by
  unfold tailWord_1750704
  simp only [CollatzResearch.WordTrace]
  refine ⟨31926710324752939641993583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42568947099670586189324777 31926710324752939641993583)
  ·
    refine ⟨47890065487129409462990375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31926710324752939641993583 47890065487129409462990375)
    ·
      refine ⟨71835098230694114194485563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47890065487129409462990375 71835098230694114194485563)
      ·
        refine ⟨107752647346041171291728345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71835098230694114194485563 107752647346041171291728345)
        ·
          refine ⟨80814485509530878468796259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107752647346041171291728345 80814485509530878468796259)
          ·
            refine ⟨121221728264296317703194389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80814485509530878468796259 121221728264296317703194389)
            ·
              refine ⟨5682268512388889892337237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121221728264296317703194389 5682268512388889892337237)
              ·
                refine ⟨66589084129557303425827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5682268512388889892337237 66589084129557303425827)
                ·
                  rfl

theorem cell22_1750704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_1750704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750704 prefixEnd_1750704 := by exact prefixLift 1750704
  have htrace : WordTrace (prefixWord ++ tailWord_1750704) baseStart_1750704 baseEnd_1750704 := by
    simpa [prefixWord, tailWord_1750704, baseEnd_1750704] using wordTrace_append hprefix tailTrace_1750704
  have hstable : (prefixWord ++ tailWord_1750704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750704).length < 2 ^ (prefixWord ++ tailWord_1750704).sum := by decide
  have hdescent : baseEnd_1750704 < baseStart_1750704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750706 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1750706 : Nat := 118140960795 + 1750706 * 2 ^ 59
def prefixEnd_1750706 : Nat := 4983230072969 + 3 ^ 40 * 1750706 * 2
def baseEnd_1750706 : Nat := 599302441806888392282437

theorem tailTrace_1750706 : CollatzResearch.WordTrace tailWord_1750706 prefixEnd_1750706 599302441806888392282437 := by
  unfold tailWord_1750706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963373398874658406389993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42568995730332422417039981 15963373398874658406389993)
  ·
    refine ⟨11972530049155993804792495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15963373398874658406389993 11972530049155993804792495)
    ·
      refine ⟨17958795073733990707188743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11972530049155993804792495 17958795073733990707188743)
      ·
        refine ⟨26938192610600986060783115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17958795073733990707188743 26938192610600986060783115)
        ·
          refine ⟨40407288915901479091174673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26938192610600986060783115 40407288915901479091174673)
          ·
            refine ⟨30305466686926109318381005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40407288915901479091174673 30305466686926109318381005)
            ·
              refine ⟨11364550007597290994392877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30305466686926109318381005 11364550007597290994392877)
              ·
                refine ⟨4261706252848984122897329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11364550007597290994392877 4261706252848984122897329)
                ·
                  refine ⟨3196279689636738092172997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4261706252848984122897329 3196279689636738092172997)
                  ·
                    refine ⟨599302441806888392282437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196279689636738092172997 599302441806888392282437)
                    ·
                      rfl

theorem cell22_1750706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1750706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750706 prefixEnd_1750706 := by exact prefixLift 1750706
  have htrace : WordTrace (prefixWord ++ tailWord_1750706) baseStart_1750706 baseEnd_1750706 := by
    simpa [prefixWord, tailWord_1750706, baseEnd_1750706] using wordTrace_append hprefix tailTrace_1750706
  have hstable : (prefixWord ++ tailWord_1750706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750706).length < 2 ^ (prefixWord ++ tailWord_1750706).sum := by decide
  have hdescent : baseEnd_1750706 < baseStart_1750706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750738 : List Nat := [3, 2, 2, 2, 2, 3, 1, 7]
def baseStart_1750738 : Nat := 118140960795 + 1750738 * 2 ^ 59
def prefixEnd_1750738 : Nat := 4983230072969 + 3 ^ 40 * 1750738 * 2
def baseEnd_1750738 : Nat := 66590377340094552831371

theorem tailTrace_1750738 : CollatzResearch.WordTrace tailWord_1750738 prefixEnd_1750738 66590377340094552831371 := by
  unfold tailWord_1750738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963665182845675772681217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42569773820921802060483245 15963665182845675772681217)
  ·
    refine ⟨11972748887134256829510913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15963665182845675772681217 11972748887134256829510913)
    ·
      refine ⟨8979561665350692622133185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11972748887134256829510913 8979561665350692622133185)
      ·
        refine ⟨6734671249013019466599889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8979561665350692622133185 6734671249013019466599889)
        ·
          refine ⟨5051003436759764599949917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6734671249013019466599889 5051003436759764599949917)
          ·
            refine ⟨1894126288784911724981219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5051003436759764599949917 1894126288784911724981219)
            ·
              refine ⟨2841189433177367587471829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894126288784911724981219 2841189433177367587471829)
              ·
                refine ⟨66590377340094552831371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2841189433177367587471829 66590377340094552831371)
                ·
                  rfl

theorem cell22_1750738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_1750738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750738 prefixEnd_1750738 := by exact prefixLift 1750738
  have htrace : WordTrace (prefixWord ++ tailWord_1750738) baseStart_1750738 baseEnd_1750738 := by
    simpa [prefixWord, tailWord_1750738, baseEnd_1750738] using wordTrace_append hprefix tailTrace_1750738
  have hstable : (prefixWord ++ tailWord_1750738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750738).length < 2 ^ (prefixWord ++ tailWord_1750738).sum := by decide
  have hdescent : baseEnd_1750738 < baseStart_1750738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750742 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1750742 : Nat := 118140960795 + 1750742 * 2 ^ 59
def prefixEnd_1750742 : Nat := 4983230072969 + 3 ^ 40 * 1750742 * 2
def baseEnd_1750742 : Nat := 599314765342596298382327

theorem tailTrace_1750742 : CollatzResearch.WordTrace tailWord_1750742 prefixEnd_1750742 599314765342596298382327 := by
  unfold tailWord_1750742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990925413960513235866905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42569871082245474515913653 3990925413960513235866905)
  ·
    refine ⟨2993194060470384926900179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3990925413960513235866905 2993194060470384926900179)
    ·
      refine ⟨4489791090705577390350269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993194060470384926900179 4489791090705577390350269)
      ·
        refine ⟨1683671659014591521381351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4489791090705577390350269 1683671659014591521381351)
        ·
          refine ⟨2525507488521887282072027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683671659014591521381351 2525507488521887282072027)
          ·
            refine ⟨3788261232782830923108041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525507488521887282072027 3788261232782830923108041)
            ·
              refine ⟨2841195924587123192331031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788261232782830923108041 2841195924587123192331031)
              ·
                refine ⟨4261793886880684788496547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841195924587123192331031 4261793886880684788496547)
                ·
                  refine ⟨6392690830321027182744821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261793886880684788496547 6392690830321027182744821)
                  ·
                    refine ⟨599314765342596298382327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6392690830321027182744821 599314765342596298382327)
                    ·
                      rfl

theorem cell22_1750742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1750742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750742 prefixEnd_1750742 := by exact prefixLift 1750742
  have htrace : WordTrace (prefixWord ++ tailWord_1750742) baseStart_1750742 baseEnd_1750742 := by
    simpa [prefixWord, tailWord_1750742, baseEnd_1750742] using wordTrace_append hprefix tailTrace_1750742
  have hstable : (prefixWord ++ tailWord_1750742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750742).length < 2 ^ (prefixWord ++ tailWord_1750742).sum := by decide
  have hdescent : baseEnd_1750742 < baseStart_1750742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750766 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_1750766 : Nat := 118140960795 + 1750766 * 2 ^ 59
def prefixEnd_1750766 : Nat := 4983230072969 + 3 ^ 40 * 1750766 * 2
def baseEnd_1750766 : Nat := 199774327011022745260751

theorem tailTrace_1750766 : CollatzResearch.WordTrace tailWord_1750766 prefixEnd_1750766 199774327011022745260751 := by
  unfold tailWord_1750766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981960246910157984093019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42570454650187509248496101 7981960246910157984093019)
  ·
    refine ⟨11972940370365236976139529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7981960246910157984093019 11972940370365236976139529)
    ·
      refine ⟨8979705277773927732104647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11972940370365236976139529 8979705277773927732104647)
      ·
        refine ⟨13469557916660891598156971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8979705277773927732104647 13469557916660891598156971)
        ·
          refine ⟨20204336874991337397235457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13469557916660891598156971 20204336874991337397235457)
          ·
            refine ⟨15153252656243503047926593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20204336874991337397235457 15153252656243503047926593)
            ·
              refine ⟨11364939492182627285944945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15153252656243503047926593 11364939492182627285944945)
              ·
                refine ⟨8523704619136970464458709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364939492182627285944945 8523704619136970464458709)
                ·
                  refine ⟨199774327011022745260751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8523704619136970464458709 199774327011022745260751)
                  ·
                    rfl

theorem cell22_1750766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_1750766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750766 prefixEnd_1750766 := by exact prefixLift 1750766
  have htrace : WordTrace (prefixWord ++ tailWord_1750766) baseStart_1750766 baseEnd_1750766 := by
    simpa [prefixWord, tailWord_1750766, baseEnd_1750766] using wordTrace_append hprefix tailTrace_1750766
  have hstable : (prefixWord ++ tailWord_1750766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750766).length < 2 ^ (prefixWord ++ tailWord_1750766).sum := by decide
  have hdescent : baseEnd_1750766 < baseStart_1750766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750796 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_1750796 : Nat := 118140960795 + 1750796 * 2 ^ 59
def prefixEnd_1750796 : Nat := 4983230072969 + 3 ^ 40 * 1750796 * 2
def baseEnd_1750796 : Nat := 599333250646158157532161

theorem tailTrace_1750796 : CollatzResearch.WordTrace tailWord_1750796 prefixEnd_1750796 599333250646158157532161 := by
  unfold tailWord_1750796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928388082586289498168121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42571184110115052664224161 31928388082586289498168121)
  ·
    refine ⟨23946291061939717123626091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31928388082586289498168121 23946291061939717123626091)
    ·
      refine ⟨35919436592909575685439137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23946291061939717123626091 35919436592909575685439137)
      ·
        refine ⟨26939577444682181764079353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35919436592909575685439137 26939577444682181764079353)
        ·
          refine ⟨20204683083511636323059515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26939577444682181764079353 20204683083511636323059515)
          ·
            refine ⟨30307024625267454484589273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20204683083511636323059515 30307024625267454484589273)
            ·
              refine ⟨22730268468950590863441955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30307024625267454484589273 22730268468950590863441955)
              ·
                refine ⟨34095402703425886295162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22730268468950590863441955 34095402703425886295162933)
                ·
                  refine ⟨3196444003446176840171525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34095402703425886295162933 3196444003446176840171525)
                  ·
                    refine ⟨599333250646158157532161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196444003446176840171525 599333250646158157532161)
                    ·
                      rfl

theorem cell22_1750796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_1750796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750796 prefixEnd_1750796 := by exact prefixLift 1750796
  have htrace : WordTrace (prefixWord ++ tailWord_1750796) baseStart_1750796 baseEnd_1750796 := by
    simpa [prefixWord, tailWord_1750796, baseEnd_1750796] using wordTrace_append hprefix tailTrace_1750796
  have hstable : (prefixWord ++ tailWord_1750796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750796).length < 2 ^ (prefixWord ++ tailWord_1750796).sum := by decide
  have hdescent : baseEnd_1750796 < baseStart_1750796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750845 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1750845 : Nat := 118140960795 + 1750845 * 2 ^ 59
def prefixEnd_1750845 : Nat := 4983230072969 + 3 ^ 40 * 1750845 * 2
def baseEnd_1750845 : Nat := 199783341449179454352337

theorem tailTrace_1750845 : CollatzResearch.WordTrace tailWord_1750845 prefixEnd_1750845 199783341449179454352337 := by
  unfold tailWord_1750845
  simp only [CollatzResearch.WordTrace]
  refine ⟨63858563341995060364869989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42572375561330040243246659 63858563341995060364869989)
  ·
    refine ⟨11973480626624073818413123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63858563341995060364869989 11973480626624073818413123)
    ·
      refine ⟨17960220939936110727619685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11973480626624073818413123 17960220939936110727619685)
      ·
        refine ⟨3367541426238020761428691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17960220939936110727619685 3367541426238020761428691)
        ·
          refine ⟨5051312139357031142143037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367541426238020761428691 5051312139357031142143037)
          ·
            refine ⟨1894242052258886678303639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5051312139357031142143037 1894242052258886678303639)
            ·
              refine ⟨2841363078388330017455459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894242052258886678303639 2841363078388330017455459)
              ·
                refine ⟨4262044617582495026183189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841363078388330017455459 4262044617582495026183189)
                ·
                  refine ⟨199783341449179454352337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4262044617582495026183189 199783341449179454352337)
                  ·
                    rfl

theorem cell22_1750845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1750845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750845 prefixEnd_1750845 := by exact prefixLift 1750845
  have htrace : WordTrace (prefixWord ++ tailWord_1750845) baseStart_1750845 baseEnd_1750845 := by
    simpa [prefixWord, tailWord_1750845, baseEnd_1750845] using wordTrace_append hprefix tailTrace_1750845
  have hstable : (prefixWord ++ tailWord_1750845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750845).length < 2 ^ (prefixWord ++ tailWord_1750845).sum := by decide
  have hdescent : baseEnd_1750845 < baseStart_1750845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750856 : List Nat := [2, 1, 3, 1, 1, 4, 1, 9]
def baseStart_1750856 : Nat := 118140960795 + 1750856 * 2 ^ 59
def prefixEnd_1750856 : Nat := 4983230072969 + 3 ^ 40 * 1750856 * 2
def baseEnd_1750856 : Nat := 66594865541370889003553

theorem tailTrace_1750856 : CollatzResearch.WordTrace tailWord_1750856 prefixEnd_1750856 66594865541370889003553 := by
  unfold tailWord_1750856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929482272477604621760211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42572643029970139495680281 31929482272477604621760211)
  ·
    refine ⟨47894223408716406932640317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31929482272477604621760211 47894223408716406932640317)
    ·
      refine ⟨17960333778268652599740119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47894223408716406932640317 17960333778268652599740119)
      ·
        refine ⟨26940500667402978899610179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17960333778268652599740119 26940500667402978899610179)
        ·
          refine ⟨40410751001104468349415269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26940500667402978899610179 40410751001104468349415269)
          ·
            refine ⟨7577015812707087815515363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40410751001104468349415269 7577015812707087815515363)
            ·
              refine ⟨11365523719060631723273045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577015812707087815515363 11365523719060631723273045)
              ·
                refine ⟨66594865541370889003553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11365523719060631723273045 66594865541370889003553)
                ·
                  rfl

theorem cell22_1750856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 9].length) (baseStart_1750856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750856 prefixEnd_1750856 := by exact prefixLift 1750856
  have htrace : WordTrace (prefixWord ++ tailWord_1750856) baseStart_1750856 baseEnd_1750856 := by
    simpa [prefixWord, tailWord_1750856, baseEnd_1750856] using wordTrace_append hprefix tailTrace_1750856
  have hstable : (prefixWord ++ tailWord_1750856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750856).length < 2 ^ (prefixWord ++ tailWord_1750856).sum := by decide
  have hdescent : baseEnd_1750856 < baseStart_1750856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750890 : List Nat := [3, 1, 3, 4, 2, 9]
def baseStart_1750890 : Nat := 118140960795 + 1750890 * 2 ^ 59
def prefixEnd_1750890 : Nat := 4983230072969 + 3 ^ 40 * 1750890 * 2
def baseEnd_1750890 : Nat := 7399573194656459823233

theorem tailTrace_1750890 : CollatzResearch.WordTrace tailWord_1750890 prefixEnd_1750890 7399573194656459823233 := by
  unfold tailWord_1750890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965051156708008262564531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42573469751221355366838749 15965051156708008262564531)
  ·
    refine ⟨23947576735062012393846797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15965051156708008262564531 23947576735062012393846797)
    ·
      refine ⟨8980341275648254647692549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23947576735062012393846797 8980341275648254647692549)
      ·
        refine ⟨1683813989184047746442353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8980341275648254647692549 1683813989184047746442353)
        ·
          refine ⟨1262860491888035809831765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683813989184047746442353 1262860491888035809831765)
          ·
            refine ⟨7399573194656459823233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1262860491888035809831765 7399573194656459823233)
            ·
              rfl

theorem cell22_1750890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 9].length) (baseStart_1750890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750890 prefixEnd_1750890 := by exact prefixLift 1750890
  have htrace : WordTrace (prefixWord ++ tailWord_1750890) baseStart_1750890 baseEnd_1750890 := by
    simpa [prefixWord, tailWord_1750890, baseEnd_1750890] using wordTrace_append hprefix tailTrace_1750890
  have hstable : (prefixWord ++ tailWord_1750890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750890).length < 2 ^ (prefixWord ++ tailWord_1750890).sum := by decide
  have hdescent : baseEnd_1750890 < baseStart_1750890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750922 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_1750922 : Nat := 118140960795 + 1750922 * 2 ^ 59
def prefixEnd_1750922 : Nat := 4983230072969 + 3 ^ 40 * 1750922 * 2
def baseEnd_1750922 : Nat := 599376383021135828881775

theorem tailTrace_1750922 : CollatzResearch.WordTrace tailWord_1750922 prefixEnd_1750922 599376383021135828881775 := by
  unfold tailWord_1750922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965342940679025628855755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42574247841810735010282013 15965342940679025628855755)
  ·
    refine ⟨23948014411018538443283633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15965342940679025628855755 23948014411018538443283633)
    ·
      refine ⟨17961010808263903832462725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23948014411018538443283633 17961010808263903832462725)
      ·
        refine ⟨3367689526549481968586761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17961010808263903832462725 3367689526549481968586761)
        ·
          refine ⟨2525767144912111476440071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367689526549481968586761 2525767144912111476440071)
          ·
            refine ⟨3788650717368167214660107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525767144912111476440071 3788650717368167214660107)
            ·
              refine ⟨5682976076052250821990161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788650717368167214660107 5682976076052250821990161)
              ·
                refine ⟨4262232057039188116492621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682976076052250821990161 4262232057039188116492621)
                ·
                  refine ⟨1598337021389695543684733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4262232057039188116492621 1598337021389695543684733)
                  ·
                    refine ⟨599376383021135828881775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1598337021389695543684733 599376383021135828881775)
                    ·
                      rfl

theorem cell22_1750922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_1750922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750922 prefixEnd_1750922 := by exact prefixLift 1750922
  have htrace : WordTrace (prefixWord ++ tailWord_1750922) baseStart_1750922 baseEnd_1750922 := by
    simpa [prefixWord, tailWord_1750922, baseEnd_1750922] using wordTrace_append hprefix tailTrace_1750922
  have hstable : (prefixWord ++ tailWord_1750922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750922).length < 2 ^ (prefixWord ++ tailWord_1750922).sum := by decide
  have hdescent : baseEnd_1750922 < baseStart_1750922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750952 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 7]
def baseStart_1750952 : Nat := 118140960795 + 1750952 * 2 ^ 59
def prefixEnd_1750952 : Nat := 4983230072969 + 3 ^ 40 * 1750952 * 2
def baseEnd_1750952 : Nat := 199795550878075250210561

theorem tailTrace_1750952 : CollatzResearch.WordTrace tailWord_1750952 prefixEnd_1750952 199795550878075250210561 := by
  unfold tailWord_1750952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31931232976303708819507555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42574977301738278426010073 31931232976303708819507555)
  ·
    refine ⟨47896849464455563229261333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31931232976303708819507555 47896849464455563229261333)
    ·
      refine ⟨2245164818646354526371625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47896849464455563229261333 2245164818646354526371625)
      ·
        refine ⟨1683873613984765894778719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2245164818646354526371625 1683873613984765894778719)
        ·
          refine ⟨2525810420977148842168079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683873613984765894778719 2525810420977148842168079)
          ·
            refine ⟨3788715631465723263252119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525810420977148842168079 3788715631465723263252119)
            ·
              refine ⟨5683073447198584894878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788715631465723263252119 5683073447198584894878179)
              ·
                refine ⟨8524610170797877342317269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5683073447198584894878179 8524610170797877342317269)
                ·
                  refine ⟨199795550878075250210561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8524610170797877342317269 199795550878075250210561)
                  ·
                    rfl

theorem cell22_1750952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_1750952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750952 prefixEnd_1750952 := by exact prefixLift 1750952
  have htrace : WordTrace (prefixWord ++ tailWord_1750952) baseStart_1750952 baseEnd_1750952 := by
    simpa [prefixWord, tailWord_1750952, baseEnd_1750952] using wordTrace_append hprefix tailTrace_1750952
  have hstable : (prefixWord ++ tailWord_1750952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750952).length < 2 ^ (prefixWord ++ tailWord_1750952).sum := by decide
  have hdescent : baseEnd_1750952 < baseStart_1750952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750963 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 6]
def baseStart_1750963 : Nat := 118140960795 + 1750963 * 2 ^ 59
def prefixEnd_1750963 : Nat := 4983230072969 + 3 ^ 40 * 1750963 * 2
def baseEnd_1750963 : Nat := 199796806053008462868883

theorem tailTrace_1750963 : CollatzResearch.WordTrace tailWord_1750963 prefixEnd_1750963 199796806053008462868883 := by
  unfold tailWord_1750963
  simp only [CollatzResearch.WordTrace]
  refine ⟨63862867155567566517665543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42575244770378377678443695 63862867155567566517665543)
  ·
    refine ⟨95794300733351349776498315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63862867155567566517665543 95794300733351349776498315)
    ·
      refine ⟨143691451100027024664747473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95794300733351349776498315 143691451100027024664747473)
      ·
        refine ⟨107768588325020268498560605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143691451100027024664747473 107768588325020268498560605)
        ·
          refine ⟨40413220621882600686960227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107768588325020268498560605 40413220621882600686960227)
          ·
            refine ⟨60619830932823901030440341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40413220621882600686960227 60619830932823901030440341)
            ·
              refine ⟨2841554574976120360801891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60619830932823901030440341 2841554574976120360801891)
              ·
                refine ⟨4262331862464180541202837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841554574976120360801891 4262331862464180541202837)
                ·
                  refine ⟨199796806053008462868883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4262331862464180541202837 199796806053008462868883)
                  ·
                    rfl

theorem cell22_1750963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 6].length) (baseStart_1750963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750963 prefixEnd_1750963 := by exact prefixLift 1750963
  have htrace : WordTrace (prefixWord ++ tailWord_1750963) baseStart_1750963 baseEnd_1750963 := by
    simpa [prefixWord, tailWord_1750963, baseEnd_1750963] using wordTrace_append hprefix tailTrace_1750963
  have hstable : (prefixWord ++ tailWord_1750963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750963).length < 2 ^ (prefixWord ++ tailWord_1750963).sum := by decide
  have hdescent : baseEnd_1750963 < baseStart_1750963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750997 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 4]
def baseStart_1750997 : Nat := 118140960795 + 1750997 * 2 ^ 59
def prefixEnd_1750997 : Nat := 4983230072969 + 3 ^ 40 * 1750997 * 2
def baseEnd_1750997 : Nat := 199800685684620211085515

theorem tailTrace_1750997 : CollatzResearch.WordTrace tailWord_1750997 prefixEnd_1750997 199800685684620211085515 := by
  unfold tailWord_1750997
  simp only [CollatzResearch.WordTrace]
  refine ⟨63864107237444390324403245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42576071491629593549602163 63864107237444390324403245)
  ·
    refine ⟨23949040214041646371651217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63864107237444390324403245 23949040214041646371651217)
    ·
      refine ⟨17961780160531234778738413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23949040214041646371651217 17961780160531234778738413)
      ·
        refine ⟨6735667560199213042026905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17961780160531234778738413 6735667560199213042026905)
        ·
          refine ⟨5051750670149409781520179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6735667560199213042026905 5051750670149409781520179)
          ·
            refine ⟨7577626005224114672280269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051750670149409781520179 7577626005224114672280269)
            ·
              refine ⟨2841609751959043002105101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7577626005224114672280269 2841609751959043002105101)
              ·
                refine ⟨1065603656984641125789413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2841609751959043002105101 1065603656984641125789413)
                ·
                  refine ⟨199800685684620211085515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065603656984641125789413 199800685684620211085515)
                  ·
                    rfl

theorem cell22_1750997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_1750997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1750997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1750997 prefixEnd_1750997 := by exact prefixLift 1750997
  have htrace : WordTrace (prefixWord ++ tailWord_1750997) baseStart_1750997 baseEnd_1750997 := by
    simpa [prefixWord, tailWord_1750997, baseEnd_1750997] using wordTrace_append hprefix tailTrace_1750997
  have hstable : (prefixWord ++ tailWord_1750997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750997).length < 2 ^ (prefixWord ++ tailWord_1750997).sum := by decide
  have hdescent : baseEnd_1750997 < baseStart_1750997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751025 : List Nat := [1, 2, 2, 2, 5, 1, 2, 7]
def baseStart_1751025 : Nat := 118140960795 + 1751025 * 2 ^ 59
def prefixEnd_1751025 : Nat := 4983230072969 + 3 ^ 40 * 1751025 * 2
def baseEnd_1751025 : Nat := 66601293558453099284051

theorem tailTrace_1751025 : CollatzResearch.WordTrace tailWord_1751025 prefixEnd_1751025 66601293558453099284051 := by
  unfold tailWord_1751025
  simp only [CollatzResearch.WordTrace]
  refine ⟨63865128481342951106422529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42576752320895300737615019 63865128481342951106422529)
  ·
    refine ⟨47898846361007213329816897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63865128481342951106422529 47898846361007213329816897)
    ·
      refine ⟨35924134770755409997362673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47898846361007213329816897 35924134770755409997362673)
      ·
        refine ⟨26943101078066557498022005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35924134770755409997362673 26943101078066557498022005)
        ·
          refine ⟨2525915726068739765439563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26943101078066557498022005 2525915726068739765439563)
          ·
            refine ⟨3788873589103109648159345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525915726068739765439563 3788873589103109648159345)
            ·
              refine ⟨2841655191827332236119509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788873589103109648159345 2841655191827332236119509)
              ·
                refine ⟨66601293558453099284051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2841655191827332236119509 66601293558453099284051)
                ·
                  rfl

theorem cell22_1751025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 7].length) (baseStart_1751025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751025 prefixEnd_1751025 := by exact prefixLift 1751025
  have htrace : WordTrace (prefixWord ++ tailWord_1751025) baseStart_1751025 baseEnd_1751025 := by
    simpa [prefixWord, tailWord_1751025, baseEnd_1751025] using wordTrace_append hprefix tailTrace_1751025
  have hstable : (prefixWord ++ tailWord_1751025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751025).length < 2 ^ (prefixWord ++ tailWord_1751025).sum := by decide
  have hdescent : baseEnd_1751025 < baseStart_1751025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751044 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1751044 : Nat := 118140960795 + 1751044 * 2 ^ 59
def prefixEnd_1751044 : Nat := 4983230072969 + 3 ^ 40 * 1751044 * 2
def baseEnd_1751044 : Nat := 599418146114368177331401

theorem tailTrace_1751044 : CollatzResearch.WordTrace tailWord_1751044 prefixEnd_1751044 599418146114368177331401 := by
  unfold tailWord_1751044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31932910734137058675682093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42577214312182744900909457 31932910734137058675682093)
  ·
    refine ⟨11974841525301397003380785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31932910734137058675682093 11974841525301397003380785)
    ·
      refine ⟨8981131143976047752535589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11974841525301397003380785 8981131143976047752535589)
      ·
        refine ⟨1683962089495508953600423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8981131143976047752535589 1683962089495508953600423)
        ·
          refine ⟨2525943134243263430400635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683962089495508953600423 2525943134243263430400635)
          ·
            refine ⟨3788914701364895145600953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525943134243263430400635 3788914701364895145600953)
            ·
              refine ⟨2841686026023671359200715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788914701364895145600953 2841686026023671359200715)
              ·
                refine ⟨4262529039035507038801073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841686026023671359200715 4262529039035507038801073)
                ·
                  refine ⟨3196896779276630279100805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262529039035507038801073 3196896779276630279100805)
                  ·
                    refine ⟨599418146114368177331401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196896779276630279100805 599418146114368177331401)
                    ·
                      rfl

theorem cell22_1751044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1751044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751044 prefixEnd_1751044 := by exact prefixLift 1751044
  have htrace : WordTrace (prefixWord ++ tailWord_1751044) baseStart_1751044 baseEnd_1751044 := by
    simpa [prefixWord, tailWord_1751044, baseEnd_1751044] using wordTrace_append hprefix tailTrace_1751044
  have hstable : (prefixWord ++ tailWord_1751044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751044).length < 2 ^ (prefixWord ++ tailWord_1751044).sum := by decide
  have hdescent : baseEnd_1751044 < baseStart_1751044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751074 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1751074 : Nat := 118140960795 + 1751074 * 2 ^ 59
def prefixEnd_1751074 : Nat := 4983230072969 + 3 ^ 40 * 1751074 * 2
def baseEnd_1751074 : Nat := 599428415727458099081309

theorem tailTrace_1751074 : CollatzResearch.WordTrace tailWord_1751074 prefixEnd_1751074 599428415727458099081309 := by
  unfold tailWord_1751074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966728914541358118739069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42577943772110288316637517 15966728914541358118739069)
  ·
    refine ⟨5987523342953009294527151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15966728914541358118739069 5987523342953009294527151)
    ·
      refine ⟨8981285014429513941790727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987523342953009294527151 8981285014429513941790727)
      ·
        refine ⟨13471927521644270912686091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981285014429513941790727 13471927521644270912686091)
        ·
          refine ⟨20207891282466406369029137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13471927521644270912686091 20207891282466406369029137)
          ·
            refine ⟨15155918461849804776771853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20207891282466406369029137 15155918461849804776771853)
            ·
              refine ⟨5683469423193676791289445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15155918461849804776771853 5683469423193676791289445)
              ·
                refine ⟨1065650516848814398366771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5683469423193676791289445 1065650516848814398366771)
                ·
                  refine ⟨1598475775273221597550157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065650516848814398366771 1598475775273221597550157)
                  ·
                    refine ⟨599428415727458099081309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1598475775273221597550157 599428415727458099081309)
                    ·
                      rfl

theorem cell22_1751074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1751074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751074 prefixEnd_1751074 := by exact prefixLift 1751074
  have htrace : WordTrace (prefixWord ++ tailWord_1751074) baseStart_1751074 baseEnd_1751074 := by
    simpa [prefixWord, tailWord_1751074, baseEnd_1751074] using wordTrace_append hprefix tailTrace_1751074
  have hstable : (prefixWord ++ tailWord_1751074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751074).length < 2 ^ (prefixWord ++ tailWord_1751074).sum := by decide
  have hdescent : baseEnd_1751074 < baseStart_1751074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751100 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1751100 : Nat := 118140960795 + 1751100 * 2 ^ 59
def prefixEnd_1751100 : Nat := 4983230072969 + 3 ^ 40 * 1751100 * 2
def baseEnd_1751100 : Nat := 599437316058802697931229

theorem tailTrace_1751100 : CollatzResearch.WordTrace tailWord_1751100 prefixEnd_1751100 599437316058802697931229 := by
  unfold tailWord_1751100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31933931978035619457701377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42578575970714159276935169 31933931978035619457701377)
  ·
    refine ⟨23950448983526714593276033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31933931978035619457701377 23950448983526714593276033)
    ·
      refine ⟨17962836737645035944957025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23950448983526714593276033 17962836737645035944957025)
      ·
        refine ⟨13472127553233776958717769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17962836737645035944957025 13472127553233776958717769)
        ·
          refine ⟨10104095664925332719038327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13472127553233776958717769 10104095664925332719038327)
          ·
            refine ⟨15156143497387999078557491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104095664925332719038327 15156143497387999078557491)
            ·
              refine ⟨22734215246081998617836237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15156143497387999078557491 22734215246081998617836237)
              ·
                refine ⟨8525330717280749481688589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22734215246081998617836237 8525330717280749481688589)
                ·
                  refine ⟨3196999018980281055633221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8525330717280749481688589 3196999018980281055633221)
                  ·
                    refine ⟨599437316058802697931229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196999018980281055633221 599437316058802697931229)
                    ·
                      rfl

theorem cell22_1751100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1751100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751100 prefixEnd_1751100 := by exact prefixLift 1751100
  have htrace : WordTrace (prefixWord ++ tailWord_1751100) baseStart_1751100 baseEnd_1751100 := by
    simpa [prefixWord, tailWord_1751100, baseEnd_1751100] using wordTrace_append hprefix tailTrace_1751100
  have hstable : (prefixWord ++ tailWord_1751100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751100).length < 2 ^ (prefixWord ++ tailWord_1751100).sum := by decide
  have hdescent : baseEnd_1751100 < baseStart_1751100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751132 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 6]
def baseStart_1751132 : Nat := 118140960795 + 1751132 * 2 ^ 59
def prefixEnd_1751132 : Nat := 4983230072969 + 3 ^ 40 * 1751132 * 2
def baseEnd_1751132 : Nat := 199816090104255093710377

theorem tailTrace_1751132 : CollatzResearch.WordTrace tailWord_1751132 prefixEnd_1751132 199816090104255093710377 := by
  unfold tailWord_1751132
  simp only [CollatzResearch.WordTrace]
  refine ⟨31934515545977654190283825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42579354061303538920378433 31934515545977654190283825)
  ·
    refine ⟨23950886659483240642712869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31934515545977654190283825 23950886659483240642712869)
    ·
      refine ⟨4490791248653107620508663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23950886659483240642712869 4490791248653107620508663)
      ·
        refine ⟨6736186872979661430762995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490791248653107620508663 6736186872979661430762995)
        ·
          refine ⟨10104280309469492146144493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736186872979661430762995 10104280309469492146144493)
          ·
            refine ⟨3789105116051059554804185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10104280309469492146144493 3789105116051059554804185)
            ·
              refine ⟨2841828837038294666103139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789105116051059554804185 2841828837038294666103139)
              ·
                refine ⟨4262743255557441999154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841828837038294666103139 4262743255557441999154709)
                ·
                  refine ⟨199816090104255093710377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4262743255557441999154709 199816090104255093710377)
                  ·
                    rfl

theorem cell22_1751132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_1751132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751132 prefixEnd_1751132 := by exact prefixLift 1751132
  have htrace : WordTrace (prefixWord ++ tailWord_1751132) baseStart_1751132 baseEnd_1751132 := by
    simpa [prefixWord, tailWord_1751132, baseEnd_1751132] using wordTrace_append hprefix tailTrace_1751132
  have hstable : (prefixWord ++ tailWord_1751132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751132).length < 2 ^ (prefixWord ++ tailWord_1751132).sum := by decide
  have hdescent : baseEnd_1751132 < baseStart_1751132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751254 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1751254 : Nat := 118140960795 + 1751254 * 2 ^ 59
def prefixEnd_1751254 : Nat := 4983230072969 + 3 ^ 40 * 1751254 * 2
def baseEnd_1751254 : Nat := 599490033405997629580757

theorem tailTrace_1751254 : CollatzResearch.WordTrace tailWord_1751254 prefixEnd_1751254 599490033405997629580757 := by
  unfold tailWord_1751254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992092549844582701031801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42582320531675548811005877 3992092549844582701031801)
  ·
    refine ⟨2994069412383437025773851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992092549844582701031801 2994069412383437025773851)
    ·
      refine ⟨4491104118575155538660777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994069412383437025773851 4491104118575155538660777)
      ·
        refine ⟨3368328088931366653995583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4491104118575155538660777 3368328088931366653995583)
        ·
          refine ⟨5052492133397049980993375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3368328088931366653995583 5052492133397049980993375)
          ·
            refine ⟨7578738200095574971490063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052492133397049980993375 7578738200095574971490063)
            ·
              refine ⟨11368107300143362457235095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578738200095574971490063 11368107300143362457235095)
              ·
                refine ⟨17052160950215043685852643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11368107300143362457235095 17052160950215043685852643)
                ·
                  refine ⟨25578241425322565528778965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17052160950215043685852643 25578241425322565528778965)
                  ·
                    refine ⟨599490033405997629580757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25578241425322565528778965 599490033405997629580757)
                    ·
                      rfl

theorem cell22_1751254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1751254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751254 prefixEnd_1751254 := by exact prefixLift 1751254
  have htrace : WordTrace (prefixWord ++ tailWord_1751254) baseStart_1751254 baseEnd_1751254 := by
    simpa [prefixWord, tailWord_1751254, baseEnd_1751254] using wordTrace_append hprefix tailTrace_1751254
  have hstable : (prefixWord ++ tailWord_1751254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751254).length < 2 ^ (prefixWord ++ tailWord_1751254).sum := by decide
  have hdescent : baseEnd_1751254 < baseStart_1751254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751286 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_1751286 : Nat := 118140960795 + 1751286 * 2 ^ 59
def prefixEnd_1751286 : Nat := 4983230072969 + 3 ^ 40 * 1751286 * 2
def baseEnd_1751286 : Nat := 599500987659960212780659

theorem tailTrace_1751286 : CollatzResearch.WordTrace tailWord_1751286 prefixEnd_1751286 599500987659960212780659 := by
  unfold tailWord_1751286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992165495837337042604607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42583098622264928454449141 3992165495837337042604607)
  ·
    refine ⟨5988248243756005563906911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992165495837337042604607 5988248243756005563906911)
    ·
      refine ⟨8982372365634008345860367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988248243756005563906911 8982372365634008345860367)
      ·
        refine ⟨13473558548451012518790551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982372365634008345860367 13473558548451012518790551)
        ·
          refine ⟨20210337822676518778185827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473558548451012518790551 20210337822676518778185827)
          ·
            refine ⟨30315506734014778167278741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20210337822676518778185827 30315506734014778167278741)
            ·
              refine ⟨1421039378156942726591191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30315506734014778167278741 1421039378156942726591191)
              ·
                refine ⟨2131559067235414089886787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421039378156942726591191 2131559067235414089886787)
                ·
                  refine ⟨3197338600853121134830181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131559067235414089886787 3197338600853121134830181)
                  ·
                    refine ⟨599500987659960212780659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197338600853121134830181 599500987659960212780659)
                    ·
                      rfl

theorem cell22_1751286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_1751286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751286 prefixEnd_1751286 := by exact prefixLift 1751286
  have htrace : WordTrace (prefixWord ++ tailWord_1751286) baseStart_1751286 baseEnd_1751286 := by
    simpa [prefixWord, tailWord_1751286, baseEnd_1751286] using wordTrace_append hprefix tailTrace_1751286
  have hstable : (prefixWord ++ tailWord_1751286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751286).length < 2 ^ (prefixWord ++ tailWord_1751286).sum := by decide
  have hdescent : baseEnd_1751286 < baseStart_1751286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751295 : List Nat := [1, 1, 2, 2, 1, 4, 11]
def baseStart_1751295 : Nat := 118140960795 + 1751295 * 2 ^ 59
def prefixEnd_1751295 : Nat := 4983230072969 + 3 ^ 40 * 1751295 * 2
def baseEnd_1751295 : Nat := 22203854390514340344653

theorem tailTrace_1751295 : CollatzResearch.WordTrace tailWord_1751295 prefixEnd_1751295 22203854390514340344653 := by
  unfold tailWord_1751295
  simp only [CollatzResearch.WordTrace]
  refine ⟨63874976190364787218751339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42583317460243191479167559 63874976190364787218751339)
  ·
    refine ⟨95812464285547180828127009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63874976190364787218751339 95812464285547180828127009)
    ·
      refine ⟨71859348214160385621095257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95812464285547180828127009 71859348214160385621095257)
      ·
        refine ⟨53894511160620289215821443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71859348214160385621095257 53894511160620289215821443)
        ·
          refine ⟨80841766740930433823732165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53894511160620289215821443 80841766740930433823732165)
          ·
            refine ⟨15157831263924456341949781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80841766740930433823732165 15157831263924456341949781)
            ·
              refine ⟨22203854390514340344653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15157831263924456341949781 22203854390514340344653)
              ·
                rfl

theorem cell22_1751295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 11].length) (baseStart_1751295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751295 prefixEnd_1751295 := by exact prefixLift 1751295
  have htrace : WordTrace (prefixWord ++ tailWord_1751295) baseStart_1751295 baseEnd_1751295 := by
    simpa [prefixWord, tailWord_1751295, baseEnd_1751295] using wordTrace_append hprefix tailTrace_1751295
  have hstable : (prefixWord ++ tailWord_1751295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751295).length < 2 ^ (prefixWord ++ tailWord_1751295).sum := by decide
  have hdescent : baseEnd_1751295 < baseStart_1751295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751297 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1751297 : Nat := 118140960795 + 1751297 * 2 ^ 59
def prefixEnd_1751297 : Nat := 4983230072969 + 3 ^ 40 * 1751297 * 2
def baseEnd_1751297 : Nat := 599504753184759850755625

theorem tailTrace_1751297 : CollatzResearch.WordTrace tailWord_1751297 prefixEnd_1751297 599504753184759850755625 := by
  unfold tailWord_1751297
  simp only [CollatzResearch.WordTrace]
  refine ⟨63875049136357541560324145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42583366090905027706882763 63875049136357541560324145)
  ·
    refine ⟨47906286852268156170243109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63875049136357541560324145 47906286852268156170243109)
    ·
      refine ⟨8982428784800279281920583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47906286852268156170243109 8982428784800279281920583)
      ·
        refine ⟨13473643177200418922880875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982428784800279281920583 13473643177200418922880875)
        ·
          refine ⟨20210464765800628384321313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13473643177200418922880875 20210464765800628384321313)
          ·
            refine ⟨15157848574350471288240985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20210464765800628384321313 15157848574350471288240985)
            ·
              refine ⟨11368386430762853466180739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15157848574350471288240985 11368386430762853466180739)
              ·
                refine ⟨17052579646144280199271109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11368386430762853466180739 17052579646144280199271109)
                ·
                  refine ⟨3197358683652052537363333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17052579646144280199271109 3197358683652052537363333)
                  ·
                    refine ⟨599504753184759850755625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197358683652052537363333 599504753184759850755625)
                    ·
                      rfl

theorem cell22_1751297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1751297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751297 prefixEnd_1751297 := by exact prefixLift 1751297
  have htrace : WordTrace (prefixWord ++ tailWord_1751297) baseStart_1751297 baseEnd_1751297 := by
    simpa [prefixWord, tailWord_1751297, baseEnd_1751297] using wordTrace_append hprefix tailTrace_1751297
  have hstable : (prefixWord ++ tailWord_1751297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751297).length < 2 ^ (prefixWord ++ tailWord_1751297).sum := by decide
  have hdescent : baseEnd_1751297 < baseStart_1751297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751372 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1751372 : Nat := 118140960795 + 1751372 * 2 ^ 59
def prefixEnd_1751372 : Nat := 4983230072969 + 3 ^ 40 * 1751372 * 2
def baseEnd_1751372 : Nat := 599530427217484655130395

theorem tailTrace_1751372 : CollatzResearch.WordTrace tailWord_1751372 prefixEnd_1751372 599530427217484655130395 := by
  unfold tailWord_1751372
  simp only [CollatzResearch.WordTrace]
  refine ⟨31938892305542914684652185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42585189740723886246202913 31938892305542914684652185)
  ·
    refine ⟨23954169229157186013489139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31938892305542914684652185 23954169229157186013489139)
    ·
      refine ⟨35931253843735779020233709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23954169229157186013489139 35931253843735779020233709)
      ·
        refine ⟨13474220191400917132587641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35931253843735779020233709 13474220191400917132587641)
        ·
          refine ⟨10105665143550687849440731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13474220191400917132587641 10105665143550687849440731)
          ·
            refine ⟨15158497715326031774161097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105665143550687849440731 15158497715326031774161097)
            ·
              refine ⟨11368873286494523830620823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15158497715326031774161097 11368873286494523830620823)
              ·
                refine ⟨17053309929741785745931235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11368873286494523830620823 17053309929741785745931235)
                ·
                  refine ⟨25579964894612678618896853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17053309929741785745931235 25579964894612678618896853)
                  ·
                    refine ⟨599530427217484655130395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25579964894612678618896853 599530427217484655130395)
                    ·
                      rfl

theorem cell22_1751372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1751372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751372 prefixEnd_1751372 := by exact prefixLift 1751372
  have htrace : WordTrace (prefixWord ++ tailWord_1751372) baseStart_1751372 baseEnd_1751372 := by
    simpa [prefixWord, tailWord_1751372, baseEnd_1751372] using wordTrace_append hprefix tailTrace_1751372
  have hstable : (prefixWord ++ tailWord_1751372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751372).length < 2 ^ (prefixWord ++ tailWord_1751372).sum := by decide
  have hdescent : baseEnd_1751372 < baseStart_1751372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751417 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1751417 : Nat := 118140960795 + 1751417 * 2 ^ 59
def prefixEnd_1751417 : Nat := 4983230072969 + 3 ^ 40 * 1751417 * 2
def baseEnd_1751417 : Nat := 599545831637119537755257

theorem tailTrace_1751417 : CollatzResearch.WordTrace tailWord_1751417 prefixEnd_1751417 599545831637119537755257 := by
  unfold tailWord_1751417
  simp only [CollatzResearch.WordTrace]
  refine ⟨63879425895922802054692505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42586283930615201369795003 63879425895922802054692505)
  ·
    refine ⟨47909569421942101541019379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63879425895922802054692505 47909569421942101541019379)
    ·
      refine ⟨71864354132913152311529069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47909569421942101541019379 71864354132913152311529069)
      ·
        refine ⟨26949132799842432116823401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71864354132913152311529069 26949132799842432116823401)
        ·
          refine ⟨20211849599881824087617551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26949132799842432116823401 20211849599881824087617551)
          ·
            refine ⟨30317774399822736131426327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20211849599881824087617551 30317774399822736131426327)
            ·
              refine ⟨45476661599734104197139491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30317774399822736131426327 45476661599734104197139491)
              ·
                refine ⟨68214992399601156295709237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45476661599734104197139491 68214992399601156295709237)
                ·
                  refine ⟨6395155537462608402722741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68214992399601156295709237 6395155537462608402722741)
                  ·
                    refine ⟨599545831637119537755257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6395155537462608402722741 599545831637119537755257)
                    ·
                      rfl

theorem cell22_1751417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1751417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751417 prefixEnd_1751417 := by exact prefixLift 1751417
  have htrace : WordTrace (prefixWord ++ tailWord_1751417) baseStart_1751417 baseEnd_1751417 := by
    simpa [prefixWord, tailWord_1751417, baseEnd_1751417] using wordTrace_append hprefix tailTrace_1751417
  have hstable : (prefixWord ++ tailWord_1751417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751417).length < 2 ^ (prefixWord ++ tailWord_1751417).sum := by decide
  have hdescent : baseEnd_1751417 < baseStart_1751417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751447 : List Nat := [1, 1, 3, 3, 1, 1, 2, 10]
def baseStart_1751447 : Nat := 118140960795 + 1751447 * 2 ^ 59
def prefixEnd_1751447 : Nat := 4983230072969 + 3 ^ 40 * 1751447 * 2
def baseEnd_1751447 : Nat := 66617344583356606611685

theorem tailTrace_1751447 : CollatzResearch.WordTrace tailWord_1751447 prefixEnd_1751447 66617344583356606611685 := by
  unfold tailWord_1751447
  simp only [CollatzResearch.WordTrace]
  refine ⟨63880520085814117178284595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42587013390542744785523063 63880520085814117178284595)
  ·
    refine ⟨95820780128721175767426893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63880520085814117178284595 95820780128721175767426893)
    ·
      refine ⟨35932792548270440912785085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95820780128721175767426893 35932792548270440912785085)
      ·
        refine ⟨13474797205601415342294407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35932792548270440912785085 13474797205601415342294407)
        ·
          refine ⟨20212195808402123013441611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13474797205601415342294407 20212195808402123013441611)
          ·
            refine ⟨30318293712603184520162417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20212195808402123013441611 30318293712603184520162417)
            ·
              refine ⟨22738720284452388390121813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30318293712603184520162417 22738720284452388390121813)
              ·
                refine ⟨66617344583356606611685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22738720284452388390121813 66617344583356606611685)
                ·
                  rfl

theorem cell22_1751447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 10].length) (baseStart_1751447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751447 prefixEnd_1751447 := by exact prefixLift 1751447
  have htrace : WordTrace (prefixWord ++ tailWord_1751447) baseStart_1751447 baseEnd_1751447 := by
    simpa [prefixWord, tailWord_1751447, baseEnd_1751447] using wordTrace_append hprefix tailTrace_1751447
  have hstable : (prefixWord ++ tailWord_1751447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751447).length < 2 ^ (prefixWord ++ tailWord_1751447).sum := by decide
  have hdescent : baseEnd_1751447 < baseStart_1751447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751453 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 4]
def baseStart_1751453 : Nat := 118140960795 + 1751453 * 2 ^ 59
def prefixEnd_1751453 : Nat := 4983230072969 + 3 ^ 40 * 1751453 * 2
def baseEnd_1751453 : Nat := 199852718390942481285049

theorem tailTrace_1751453 : CollatzResearch.WordTrace tailWord_1751453 prefixEnd_1751453 199852718390942481285049 := by
  unfold tailWord_1751453
  simp only [CollatzResearch.WordTrace]
  refine ⟨63880738923792380203003013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42587159282528253468668675 63880738923792380203003013)
  ·
    refine ⟨11977638548211071288063065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63880738923792380203003013 11977638548211071288063065)
    ·
      refine ⟨8983228911158303466047299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11977638548211071288063065 8983228911158303466047299)
      ·
        refine ⟨13474843366737455199070949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8983228911158303466047299 13474843366737455199070949)
        ·
          refine ⟨2526533131263272849825803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13474843366737455199070949 2526533131263272849825803)
          ·
            refine ⟨3789799696894909274738705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526533131263272849825803 3789799696894909274738705)
            ·
              refine ⟨2842349772671181956054029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789799696894909274738705 2842349772671181956054029)
              ·
                refine ⟨1065881164751693233520261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842349772671181956054029 1065881164751693233520261)
                ·
                  refine ⟨199852718390942481285049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065881164751693233520261 199852718390942481285049)
                  ·
                    rfl

theorem cell22_1751453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_1751453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751453 prefixEnd_1751453 := by exact prefixLift 1751453
  have htrace : WordTrace (prefixWord ++ tailWord_1751453) baseStart_1751453 baseEnd_1751453 := by
    simpa [prefixWord, tailWord_1751453, baseEnd_1751453] using wordTrace_append hprefix tailTrace_1751453
  have hstable : (prefixWord ++ tailWord_1751453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751453).length < 2 ^ (prefixWord ++ tailWord_1751453).sum := by decide
  have hdescent : baseEnd_1751453 < baseStart_1751453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751496 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_1751496 : Nat := 118140960795 + 1751496 * 2 ^ 59
def prefixEnd_1751496 : Nat := 4983230072969 + 3 ^ 40 * 1751496 * 2
def baseEnd_1751496 : Nat := 599572874951589665030015

theorem tailTrace_1751496 : CollatzResearch.WordTrace tailWord_1751496 prefixEnd_1751496 599572874951589665030015 := by
  unfold tailWord_1751496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31941153631318299273409171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42588204841757732364545561 31941153631318299273409171)
  ·
    refine ⟨47911730446977448910113757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31941153631318299273409171 47911730446977448910113757)
    ·
      refine ⟨17966898917616543341292659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47911730446977448910113757 17966898917616543341292659)
      ·
        refine ⟨26950348376424815011938989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17966898917616543341292659 26950348376424815011938989)
        ·
          refine ⟨10106380641159305629477121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26950348376424815011938989 10106380641159305629477121)
          ·
            refine ⟨7579785480869479222107841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106380641159305629477121 7579785480869479222107841)
            ·
              refine ⟨5684839110652109416580881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7579785480869479222107841 5684839110652109416580881)
              ·
                refine ⟨4263629332989082062435661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684839110652109416580881 4263629332989082062435661)
                ·
                  refine ⟨1598860999870905773413373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4263629332989082062435661 1598860999870905773413373)
                  ·
                    refine ⟨599572874951589665030015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1598860999870905773413373 599572874951589665030015)
                    ·
                      rfl

theorem cell22_1751496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_1751496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751496 prefixEnd_1751496 := by exact prefixLift 1751496
  have htrace : WordTrace (prefixWord ++ tailWord_1751496) baseStart_1751496 baseEnd_1751496 := by
    simpa [prefixWord, tailWord_1751496, baseEnd_1751496] using wordTrace_append hprefix tailTrace_1751496
  have hstable : (prefixWord ++ tailWord_1751496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751496).length < 2 ^ (prefixWord ++ tailWord_1751496).sum := by decide
  have hdescent : baseEnd_1751496 < baseStart_1751496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751509 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1751509 : Nat := 118140960795 + 1751509 * 2 ^ 59
def prefixEnd_1751509 : Nat := 4983230072969 + 3 ^ 40 * 1751509 * 2
def baseEnd_1751509 : Nat := 199859108372420654818325

theorem tailTrace_1751509 : CollatzResearch.WordTrace tailWord_1751509 prefixEnd_1751509 199859108372420654818325 := by
  unfold tailWord_1751509
  simp only [CollatzResearch.WordTrace]
  refine ⟨63882781411589501767041581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42588520941059667844694387 63882781411589501767041581)
  ·
    refine ⟨23956043029346063162640593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63882781411589501767041581 23956043029346063162640593)
    ·
      refine ⟨17967032272009547371980445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23956043029346063162640593 17967032272009547371980445)
      ·
        refine ⟨6737637102003580264492667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17967032272009547371980445 6737637102003580264492667)
        ·
          refine ⟨10106455653005370396739001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737637102003580264492667 10106455653005370396739001)
          ·
            refine ⟨7579841739754027797554251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106455653005370396739001 7579841739754027797554251)
            ·
              refine ⟨11369762609631041696331377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579841739754027797554251 11369762609631041696331377)
              ·
                refine ⟨8527321957223281272248533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369762609631041696331377 8527321957223281272248533)
                ·
                  refine ⟨199859108372420654818325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8527321957223281272248533 199859108372420654818325)
                  ·
                    rfl

theorem cell22_1751509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1751509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751509 prefixEnd_1751509 := by exact prefixLift 1751509
  have htrace : WordTrace (prefixWord ++ tailWord_1751509) baseStart_1751509 baseEnd_1751509 := by
    simpa [prefixWord, tailWord_1751509, baseEnd_1751509] using wordTrace_append hprefix tailTrace_1751509
  have hstable : (prefixWord ++ tailWord_1751509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751509).length < 2 ^ (prefixWord ++ tailWord_1751509).sum := by decide
  have hdescent : baseEnd_1751509 < baseStart_1751509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751539 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_1751539 : Nat := 118140960795 + 1751539 * 2 ^ 59
def prefixEnd_1751539 : Nat := 4983230072969 + 3 ^ 40 * 1751539 * 2
def baseEnd_1751539 : Nat := 599587594730351886204883

theorem tailTrace_1751539 : CollatzResearch.WordTrace tailWord_1751539 prefixEnd_1751539 599587594730351886204883 := by
  unfold tailWord_1751539
  simp only [CollatzResearch.WordTrace]
  refine ⟨63883875601480816890633671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42589250400987211260422447 63883875601480816890633671)
  ·
    refine ⟨95825813402221225335950507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63883875601480816890633671 95825813402221225335950507)
    ·
      refine ⟨143738720103331838003925761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95825813402221225335950507 143738720103331838003925761)
      ·
        refine ⟨107804040077498878502944321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143738720103331838003925761 107804040077498878502944321)
        ·
          refine ⟨80853030058124158877208241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107804040077498878502944321 80853030058124158877208241)
          ·
            refine ⟨60639772543593119157906181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80853030058124158877208241 60639772543593119157906181)
            ·
              refine ⟨11369957351923709842107409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60639772543593119157906181 11369957351923709842107409)
              ·
                refine ⟨8527468013942782381580557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369957351923709842107409 8527468013942782381580557)
                ·
                  refine ⟨3197800505228543393092709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8527468013942782381580557 3197800505228543393092709)
                  ·
                    refine ⟨599587594730351886204883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197800505228543393092709 599587594730351886204883)
                    ·
                      rfl

theorem cell22_1751539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_1751539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751539 prefixEnd_1751539 := by exact prefixLift 1751539
  have htrace : WordTrace (prefixWord ++ tailWord_1751539) baseStart_1751539 baseEnd_1751539 := by
    simpa [prefixWord, tailWord_1751539, baseEnd_1751539] using wordTrace_append hprefix tailTrace_1751539
  have hstable : (prefixWord ++ tailWord_1751539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751539).length < 2 ^ (prefixWord ++ tailWord_1751539).sum := by decide
  have hdescent : baseEnd_1751539 < baseStart_1751539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751571 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 4]
def baseStart_1751571 : Nat := 118140960795 + 1751571 * 2 ^ 59
def prefixEnd_1751571 : Nat := 4983230072969 + 3 ^ 40 * 1751571 * 2
def baseEnd_1751571 : Nat := 199866182994771489801595

theorem tailTrace_1751571 : CollatzResearch.WordTrace tailWord_1751571 prefixEnd_1751571 199866182994771489801595 := by
  unfold tailWord_1751571
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885042737364886355798567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42590028491576590903865711 63885042737364886355798567)
  ·
    refine ⟨95827564106047329533697851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63885042737364886355798567 95827564106047329533697851)
    ·
      refine ⟨143741346159070994300546777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95827564106047329533697851 143741346159070994300546777)
      ·
        refine ⟨107806009619303245725410083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143741346159070994300546777 107806009619303245725410083)
        ·
          refine ⟨161709014428954868588115125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107806009619303245725410083 161709014428954868588115125)
          ·
            refine ⟨15160220102714518930135793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161709014428954868588115125 15160220102714518930135793)
            ·
              refine ⟨11370165077035889197601845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15160220102714518930135793 11370165077035889197601845)
              ·
                refine ⟨1065952975972114612275173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11370165077035889197601845 1065952975972114612275173)
                ·
                  refine ⟨199866182994771489801595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065952975972114612275173 199866182994771489801595)
                  ·
                    rfl

theorem cell22_1751571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 4].length) (baseStart_1751571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751571 prefixEnd_1751571 := by exact prefixLift 1751571
  have htrace : WordTrace (prefixWord ++ tailWord_1751571) baseStart_1751571 baseEnd_1751571 := by
    simpa [prefixWord, tailWord_1751571, baseEnd_1751571] using wordTrace_append hprefix tailTrace_1751571
  have hstable : (prefixWord ++ tailWord_1751571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751571).length < 2 ^ (prefixWord ++ tailWord_1751571).sum := by decide
  have hdescent : baseEnd_1751571 < baseStart_1751571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751573 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_1751573 : Nat := 118140960795 + 1751573 * 2 ^ 59
def prefixEnd_1751573 : Nat := 4983230072969 + 3 ^ 40 * 1751573 * 2
def baseEnd_1751573 : Nat := 599599233625187130854779

theorem tailTrace_1751573 : CollatzResearch.WordTrace tailWord_1751573 prefixEnd_1751573 599599233625187130854779 := by
  unfold tailWord_1751573
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885115683357640697371373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42590077122238427131580915 63885115683357640697371373)
  ·
    refine ⟨23956918381259115261514265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63885115683357640697371373 23956918381259115261514265)
    ·
      refine ⟨17967688785944336446135699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23956918381259115261514265 17967688785944336446135699)
      ·
        refine ⟨26951533178916504669203549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17967688785944336446135699 26951533178916504669203549)
        ·
          refine ⟨10106824942093689250951331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26951533178916504669203549 10106824942093689250951331)
          ·
            refine ⟨15160237413140533876426997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10106824942093689250951331 15160237413140533876426997)
            ·
              refine ⟨1421272257481925050915031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15160237413140533876426997 1421272257481925050915031)
              ·
                refine ⟨2131908386222887576372547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421272257481925050915031 2131908386222887576372547)
                ·
                  refine ⟨3197862579334331364558821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131908386222887576372547 3197862579334331364558821)
                  ·
                    refine ⟨599599233625187130854779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197862579334331364558821 599599233625187130854779)
                    ·
                      rfl

theorem cell22_1751573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_1751573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751573 prefixEnd_1751573 := by exact prefixLift 1751573
  have htrace : WordTrace (prefixWord ++ tailWord_1751573) baseStart_1751573 baseEnd_1751573 := by
    simpa [prefixWord, tailWord_1751573, baseEnd_1751573] using wordTrace_append hprefix tailTrace_1751573
  have hstable : (prefixWord ++ tailWord_1751573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751573).length < 2 ^ (prefixWord ++ tailWord_1751573).sum := by decide
  have hdescent : baseEnd_1751573 < baseStart_1751573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751622 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1751622 : Nat := 118140960795 + 1751622 * 2 ^ 59
def prefixEnd_1751622 : Nat := 4983230072969 + 3 ^ 40 * 1751622 * 2
def baseEnd_1751622 : Nat := 199872002442189112126543

theorem tailTrace_1751622 : CollatzResearch.WordTrace tailWord_1751622 prefixEnd_1751622 199872002442189112126543 := by
  unfold tailWord_1751622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996465714380628814559535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42591268573453414710603413 1996465714380628814559535)
  ·
    refine ⟨2994698571570943221839303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996465714380628814559535 2994698571570943221839303)
    ·
      refine ⟨4492047857356414832758955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994698571570943221839303 4492047857356414832758955)
      ·
        refine ⟨6738071786034622249138433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492047857356414832758955 6738071786034622249138433)
        ·
          refine ⟨5053553839525966686853825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6738071786034622249138433 5053553839525966686853825)
          ·
            refine ⟨3790165379644475015140369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5053553839525966686853825 3790165379644475015140369)
            ·
              refine ⟨2842624034733356261355277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790165379644475015140369 2842624034733356261355277)
              ·
                refine ⟨1065984013025008598008229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842624034733356261355277 1065984013025008598008229)
                ·
                  refine ⟨199872002442189112126543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065984013025008598008229 199872002442189112126543)
                  ·
                    rfl

theorem cell22_1751622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1751622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751622 prefixEnd_1751622 := by exact prefixLift 1751622
  have htrace : WordTrace (prefixWord ++ tailWord_1751622) baseStart_1751622 baseEnd_1751622 := by
    simpa [prefixWord, tailWord_1751622, baseEnd_1751622] using wordTrace_append hprefix tailTrace_1751622
  have hstable : (prefixWord ++ tailWord_1751622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751622).length < 2 ^ (prefixWord ++ tailWord_1751622).sum := by decide
  have hdescent : baseEnd_1751622 < baseStart_1751622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751659 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_1751659 : Nat := 118140960795 + 1751659 * 2 ^ 59
def prefixEnd_1751659 : Nat := 4983230072969 + 3 ^ 40 * 1751659 * 2
def baseEnd_1751659 : Nat := 599628673182711573204515

theorem tailTrace_1751659 : CollatzResearch.WordTrace tailWord_1751659 prefixEnd_1751659 599628673182711573204515 := by
  unfold tailWord_1751659
  simp only [CollatzResearch.WordTrace]
  refine ⟨63888252361046077385002031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42592168240697384923334687 63888252361046077385002031)
  ·
    refine ⟨95832378541569116077503047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63888252361046077385002031 95832378541569116077503047)
    ·
      refine ⟨143748567812353674116254571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95832378541569116077503047 143748567812353674116254571)
      ·
        refine ⟨215622851718530511174381857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143748567812353674116254571 215622851718530511174381857)
        ·
          refine ⟨161717138788897883380786393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215622851718530511174381857 161717138788897883380786393)
          ·
            refine ⟨121287854091673412535589795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161717138788897883380786393 121287854091673412535589795)
            ·
              refine ⟨181931781137510118803384693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121287854091673412535589795 181931781137510118803384693)
              ·
                refine ⟨17056104481641573637817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181931781137510118803384693 17056104481641573637817315)
                ·
                  refine ⟨25584156722462360456725973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17056104481641573637817315 25584156722462360456725973)
                  ·
                    refine ⟨599628673182711573204515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25584156722462360456725973 599628673182711573204515)
                    ·
                      rfl

theorem cell22_1751659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_1751659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751659 prefixEnd_1751659 := by exact prefixLift 1751659
  have htrace : WordTrace (prefixWord ++ tailWord_1751659) baseStart_1751659 baseEnd_1751659 := by
    simpa [prefixWord, tailWord_1751659, baseEnd_1751659] using wordTrace_append hprefix tailTrace_1751659
  have hstable : (prefixWord ++ tailWord_1751659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751659).length < 2 ^ (prefixWord ++ tailWord_1751659).sum := by decide
  have hdescent : baseEnd_1751659 < baseStart_1751659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751712 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_1751712 : Nat := 118140960795 + 1751712 * 2 ^ 59
def prefixEnd_1751712 : Nat := 4983230072969 + 3 ^ 40 * 1751712 * 2
def baseEnd_1751712 : Nat := 199882272055279033876451

theorem tailTrace_1751712 : CollatzResearch.WordTrace tailWord_1751712 prefixEnd_1751712 199882272055279033876451 := by
  unfold tailWord_1751712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31945092714927033718340695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42593456953236044957787593 31945092714927033718340695)
  ·
    refine ⟨47917639072390550577511043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31945092714927033718340695 47917639072390550577511043)
    ·
      refine ⟨71876458608585825866266565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47917639072390550577511043 71876458608585825866266565)
      ·
        refine ⟨13476835989109842349924981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71876458608585825866266565 13476835989109842349924981)
        ·
          refine ⟨1263453373979047720305467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13476835989109842349924981 1263453373979047720305467)
          ·
            refine ⟨1895180060968571580458201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263453373979047720305467 1895180060968571580458201)
            ·
              refine ⟨1421385045726428685343651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895180060968571580458201 1421385045726428685343651)
              ·
                refine ⟨2132077568589643028015477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421385045726428685343651 2132077568589643028015477)
                ·
                  refine ⟨199882272055279033876451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2132077568589643028015477 199882272055279033876451)
                  ·
                    rfl

theorem cell22_1751712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_1751712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751712 prefixEnd_1751712 := by exact prefixLift 1751712
  have htrace : WordTrace (prefixWord ++ tailWord_1751712) baseStart_1751712 baseEnd_1751712 := by
    simpa [prefixWord, tailWord_1751712, baseEnd_1751712] using wordTrace_append hprefix tailTrace_1751712
  have hstable : (prefixWord ++ tailWord_1751712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751712).length < 2 ^ (prefixWord ++ tailWord_1751712).sum := by decide
  have hdescent : baseEnd_1751712 < baseStart_1751712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751725 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1751725 : Nat := 118140960795 + 1751725 * 2 ^ 59
def prefixEnd_1751725 : Nat := 4983230072969 + 3 ^ 40 * 1751725 * 2
def baseEnd_1751725 : Nat := 599651266331509401054313

theorem tailTrace_1751725 : CollatzResearch.WordTrace tailWord_1751725 prefixEnd_1751725 599651266331509401054313 := by
  unfold tailWord_1751725
  simp only [CollatzResearch.WordTrace]
  refine ⟨63890659578806970656904629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42593773052537980437936419 63890659578806970656904629)
  ·
    refine ⟨5989749335513153499084809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63890659578806970656904629 5989749335513153499084809)
    ·
      refine ⟨4492312001634865124313607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5989749335513153499084809 4492312001634865124313607)
      ·
        refine ⟨6738468002452297686470411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492312001634865124313607 6738468002452297686470411)
        ·
          refine ⟨10107702003678446529705617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6738468002452297686470411 10107702003678446529705617)
          ·
            refine ⟨7580776502758834897279213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10107702003678446529705617 7580776502758834897279213)
            ·
              refine ⟨2842791188534563086479705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7580776502758834897279213 2842791188534563086479705)
              ·
                refine ⟨2132093391400922314859779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842791188534563086479705 2132093391400922314859779)
                ·
                  refine ⟨3198140087101383472289669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132093391400922314859779 3198140087101383472289669)
                  ·
                    refine ⟨599651266331509401054313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3198140087101383472289669 599651266331509401054313)
                    ·
                      rfl

theorem cell22_1751725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1751725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751725 prefixEnd_1751725 := by exact prefixLift 1751725
  have htrace : WordTrace (prefixWord ++ tailWord_1751725) baseStart_1751725 baseEnd_1751725 := by
    simpa [prefixWord, tailWord_1751725, baseEnd_1751725] using wordTrace_append hprefix tailTrace_1751725
  have hstable : (prefixWord ++ tailWord_1751725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751725).length < 2 ^ (prefixWord ++ tailWord_1751725).sum := by decide
  have hdescent : baseEnd_1751725 < baseStart_1751725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751750 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1751750 : Nat := 118140960795 + 1751750 * 2 ^ 59
def prefixEnd_1751750 : Nat := 4983230072969 + 3 ^ 40 * 1751750 * 2
def baseEnd_1751750 : Nat := 599659824342417669179237

theorem tailTrace_1751750 : CollatzResearch.WordTrace tailWord_1751750 prefixEnd_1751750 599659824342417669179237 := by
  unfold tailWord_1751750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1996611606366137497705147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42594380935810933284376469 1996611606366137497705147)
  ·
    refine ⟨2994917409549206246557721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1996611606366137497705147 2994917409549206246557721)
    ·
      refine ⟨2246188057161904684918291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2994917409549206246557721 2246188057161904684918291)
      ·
        refine ⟨3369282085742857027377437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246188057161904684918291 3369282085742857027377437)
        ·
          refine ⟨1263480782153571385266539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3369282085742857027377437 1263480782153571385266539)
          ·
            refine ⟨1895221173230357077899809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263480782153571385266539 1895221173230357077899809)
            ·
              refine ⟨1421415879922767808424857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895221173230357077899809 1421415879922767808424857)
              ·
                refine ⟨1066061909942075856318643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421415879922767808424857 1066061909942075856318643)
                ·
                  refine ⟨1599092864913113784477965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066061909942075856318643 1599092864913113784477965)
                  ·
                    refine ⟨599659824342417669179237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599092864913113784477965 599659824342417669179237)
                    ·
                      rfl

theorem cell22_1751750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1751750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751750 prefixEnd_1751750 := by exact prefixLift 1751750
  have htrace : WordTrace (prefixWord ++ tailWord_1751750) baseStart_1751750 baseEnd_1751750 := by
    simpa [prefixWord, tailWord_1751750, baseEnd_1751750] using wordTrace_append hprefix tailTrace_1751750
  have hstable : (prefixWord ++ tailWord_1751750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751750).length < 2 ^ (prefixWord ++ tailWord_1751750).sum := by decide
  have hdescent : baseEnd_1751750 < baseStart_1751750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751768 : List Nat := [2, 1, 2, 2, 3, 4, 1, 7]
def baseStart_1751768 : Nat := 118140960795 + 1751768 * 2 ^ 59
def prefixEnd_1751768 : Nat := 4983230072969 + 3 ^ 40 * 1751768 * 2
def baseEnd_1751768 : Nat := 66629554012252402469909

theorem tailTrace_1751768 : CollatzResearch.WordTrace tailWord_1751768 prefixEnd_1751768 66629554012252402469909 := by
  unfold tailWord_1751768
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946113958825594500359979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42594818611767459333813305 31946113958825594500359979)
  ·
    refine ⟨47919170938238391750539969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31946113958825594500359979 47919170938238391750539969)
    ·
      refine ⟨35939378203678793812904977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47919170938238391750539969 35939378203678793812904977)
      ·
        refine ⟨26954533652759095359678733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35939378203678793812904977 26954533652759095359678733)
        ·
          refine ⟨10107950119784660759879525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26954533652759095359678733 10107950119784660759879525)
          ·
            refine ⟨1895240647459623892477411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10107950119784660759879525 1895240647459623892477411)
            ·
              refine ⟨2842860971189435838716117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895240647459623892477411 2842860971189435838716117)
              ·
                refine ⟨66629554012252402469909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2842860971189435838716117 66629554012252402469909)
                ·
                  rfl

theorem cell22_1751768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 7].length) (baseStart_1751768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751768 prefixEnd_1751768 := by exact prefixLift 1751768
  have htrace : WordTrace (prefixWord ++ tailWord_1751768) baseStart_1751768 baseEnd_1751768 := by
    simpa [prefixWord, tailWord_1751768, baseEnd_1751768] using wordTrace_append hprefix tailTrace_1751768
  have hstable : (prefixWord ++ tailWord_1751768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751768).length < 2 ^ (prefixWord ++ tailWord_1751768).sum := by decide
  have hdescent : baseEnd_1751768 < baseStart_1751768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751772 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1751772 : Nat := 118140960795 + 1751772 * 2 ^ 59
def prefixEnd_1751772 : Nat := 4983230072969 + 3 ^ 40 * 1751772 * 2
def baseEnd_1751772 : Nat := 599667355392016945129169

theorem tailTrace_1751772 : CollatzResearch.WordTrace tailWord_1751772 prefixEnd_1751772 599667355392016945129169 := by
  unfold tailWord_1751772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946186904818348841932785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42594915873091131789243713 31946186904818348841932785)
  ·
    refine ⟨23959640178613761631449589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31946186904818348841932785 23959640178613761631449589)
    ·
      refine ⟨2246216266745040152948399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23959640178613761631449589 2246216266745040152948399)
      ·
        refine ⟨3369324400117560229422599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246216266745040152948399 3369324400117560229422599)
        ·
          refine ⟨5053986600176340344133899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369324400117560229422599 5053986600176340344133899)
          ·
            refine ⟨7580979900264510516200849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053986600176340344133899 7580979900264510516200849)
            ·
              refine ⟨5685734925198382887150637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7580979900264510516200849 5685734925198382887150637)
              ·
                refine ⟨2132150596949393582681489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5685734925198382887150637 2132150596949393582681489)
                ·
                  refine ⟨1599112947712045187011117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132150596949393582681489 1599112947712045187011117)
                  ·
                    refine ⟨599667355392016945129169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599112947712045187011117 599667355392016945129169)
                    ·
                      rfl

theorem cell22_1751772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1751772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751772 prefixEnd_1751772 := by exact prefixLift 1751772
  have htrace : WordTrace (prefixWord ++ tailWord_1751772) baseStart_1751772 baseEnd_1751772 := by
    simpa [prefixWord, tailWord_1751772, baseEnd_1751772] using wordTrace_append hprefix tailTrace_1751772
  have hstable : (prefixWord ++ tailWord_1751772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751772).length < 2 ^ (prefixWord ++ tailWord_1751772).sum := by decide
  have hdescent : baseEnd_1751772 < baseStart_1751772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751926 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1751926 : Nat := 118140960795 + 1751926 * 2 ^ 59
def prefixEnd_1751926 : Nat := 4983230072969 + 3 ^ 40 * 1751926 * 2
def baseEnd_1751926 : Nat := 199906690913070625592899

theorem tailTrace_1751926 : CollatzResearch.WordTrace tailWord_1751926 prefixEnd_1751926 199906690913070625592899 := by
  unfold tailWord_1751926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993624415692423874060727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42598660434052521323314421 3993624415692423874060727)
  ·
    refine ⟨5990436623538635811091091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993624415692423874060727 5990436623538635811091091)
    ·
      refine ⟨8985654935307953716636637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5990436623538635811091091 8985654935307953716636637)
      ·
        refine ⟨3369620600740482643738739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8985654935307953716636637 3369620600740482643738739)
        ·
          refine ⟨5054430901110723965608109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369620600740482643738739 5054430901110723965608109)
          ·
            refine ⟨1895411587916521487103041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5054430901110723965608109 1895411587916521487103041)
            ·
              refine ⟨1421558690937391115327281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895411587916521487103041 1421558690937391115327281)
              ·
                refine ⟨1066169018203043336495461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421558690937391115327281 1066169018203043336495461)
                ·
                  refine ⟨199906690913070625592899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066169018203043336495461 199906690913070625592899)
                  ·
                    rfl

theorem cell22_1751926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1751926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751926 prefixEnd_1751926 := by exact prefixLift 1751926
  have htrace : WordTrace (prefixWord ++ tailWord_1751926) baseStart_1751926 baseEnd_1751926 := by
    simpa [prefixWord, tailWord_1751926, baseEnd_1751926] using wordTrace_append hprefix tailTrace_1751926
  have hstable : (prefixWord ++ tailWord_1751926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751926).length < 2 ^ (prefixWord ++ tailWord_1751926).sum := by decide
  have hdescent : baseEnd_1751926 < baseStart_1751926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751933 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1751933 : Nat := 118140960795 + 1751933 * 2 ^ 59
def prefixEnd_1751933 : Nat := 4983230072969 + 3 ^ 40 * 1751933 * 2
def baseEnd_1751933 : Nat := 599722468982266191853675

theorem tailTrace_1751933 : CollatzResearch.WordTrace tailWord_1751933 prefixEnd_1751933 599722468982266191853675 := by
  unfold tailWord_1751933
  simp only [CollatzResearch.WordTrace]
  refine ⟨63898245962053422180476453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42598830641368948120317635 63898245962053422180476453)
  ·
    refine ⟨11980921117885016658839335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63898245962053422180476453 11980921117885016658839335)
    ·
      refine ⟨17971381676827524988259003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980921117885016658839335 17971381676827524988259003)
      ·
        refine ⟨26957072515241287482388505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17971381676827524988259003 26957072515241287482388505)
        ·
          refine ⟨20217804386430965611791379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26957072515241287482388505 20217804386430965611791379)
          ·
            refine ⟨30326706579646448417687069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20217804386430965611791379 30326706579646448417687069)
            ·
              refine ⟨11372514967367418156632651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30326706579646448417687069 11372514967367418156632651)
              ·
                refine ⟨17058772451051127234948977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372514967367418156632651 17058772451051127234948977)
                ·
                  refine ⟨12794079338288345426211733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17058772451051127234948977 12794079338288345426211733)
                  ·
                    refine ⟨599722468982266191853675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12794079338288345426211733 599722468982266191853675)
                    ·
                      rfl

theorem cell22_1751933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1751933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751933 prefixEnd_1751933 := by exact prefixLift 1751933
  have htrace : WordTrace (prefixWord ++ tailWord_1751933) baseStart_1751933 baseEnd_1751933 := by
    simpa [prefixWord, tailWord_1751933, baseEnd_1751933] using wordTrace_append hprefix tailTrace_1751933
  have hstable : (prefixWord ++ tailWord_1751933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751933).length < 2 ^ (prefixWord ++ tailWord_1751933).sum := by decide
  have hdescent : baseEnd_1751933 < baseStart_1751933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751969 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 1, 3]
def baseStart_1751969 : Nat := 118140960795 + 1751969 * 2 ^ 59
def prefixEnd_1751969 : Nat := 4983230072969 + 3 ^ 40 * 1751969 * 2
def baseEnd_1751969 : Nat := 599734792517974097953565

theorem tailTrace_1751969 : CollatzResearch.WordTrace tailWord_1751969 prefixEnd_1751969 599734792517974097953565 := by
  unfold tailWord_1751969
  simp only [CollatzResearch.WordTrace]
  refine ⟨63899558989923000328786961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42599705993282000219191307 63899558989923000328786961)
  ·
    refine ⟨47924669242442250246590221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63899558989923000328786961 47924669242442250246590221)
    ·
      refine ⟨17971750965915843842471333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47924669242442250246590221 17971750965915843842471333)
      ·
        refine ⟨3369703306109220720463375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17971750965915843842471333 3369703306109220720463375)
        ·
          refine ⟨5054554959163831080695063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369703306109220720463375 5054554959163831080695063)
          ·
            refine ⟨7581832438745746621042595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054554959163831080695063 7581832438745746621042595)
            ·
              refine ⟨11372748658118619931563893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581832438745746621042595 11372748658118619931563893)
              ·
                refine ⟨1066195186698620618584115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11372748658118619931563893 1066195186698620618584115)
                ·
                  refine ⟨1599292780047930927876173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066195186698620618584115 1599292780047930927876173)
                  ·
                    refine ⟨599734792517974097953565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599292780047930927876173 599734792517974097953565)
                    ·
                      rfl

theorem cell22_1751969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_1751969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1751969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1751969 prefixEnd_1751969 := by exact prefixLift 1751969
  have htrace : WordTrace (prefixWord ++ tailWord_1751969) baseStart_1751969 baseEnd_1751969 := by
    simpa [prefixWord, tailWord_1751969, baseEnd_1751969] using wordTrace_append hprefix tailTrace_1751969
  have hstable : (prefixWord ++ tailWord_1751969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751969).length < 2 ^ (prefixWord ++ tailWord_1751969).sum := by decide
  have hdescent : baseEnd_1751969 < baseStart_1751969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752012 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1752012 : Nat := 118140960795 + 1752012 * 2 ^ 59
def prefixEnd_1752012 : Nat := 4983230072969 + 3 ^ 40 * 1752012 * 2
def baseEnd_1752012 : Nat := 599749512296736319128433

theorem tailTrace_1752012 : CollatzResearch.WordTrace tailWord_1752012 prefixEnd_1752012 599749512296736319128433 := by
  unfold tailWord_1752012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31950563664383609336301145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42600751552511479115068193 31950563664383609336301145)
  ·
    refine ⟨23962922748287707002225859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31950563664383609336301145 23962922748287707002225859)
    ·
      refine ⟨35944384122431560503338789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23962922748287707002225859 35944384122431560503338789)
      ·
        refine ⟨6739572022955917594376023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35944384122431560503338789 6739572022955917594376023)
        ·
          refine ⟨10109358034433876391564035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739572022955917594376023 10109358034433876391564035)
          ·
            refine ⟨15164037051650814587346053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10109358034433876391564035 15164037051650814587346053)
            ·
              refine ⟨2843256947184527735127385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15164037051650814587346053 2843256947184527735127385)
              ·
                refine ⟨2132442710388395801345539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843256947184527735127385 2132442710388395801345539)
                ·
                  refine ⟨3198664065582593702018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132442710388395801345539 3198664065582593702018309)
                  ·
                    refine ⟨599749512296736319128433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3198664065582593702018309 599749512296736319128433)
                    ·
                      rfl

theorem cell22_1752012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1752012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752012 prefixEnd_1752012 := by exact prefixLift 1752012
  have htrace : WordTrace (prefixWord ++ tailWord_1752012) baseStart_1752012 baseEnd_1752012 := by
    simpa [prefixWord, tailWord_1752012, baseEnd_1752012] using wordTrace_append hprefix tailTrace_1752012
  have hstable : (prefixWord ++ tailWord_1752012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752012).length < 2 ^ (prefixWord ++ tailWord_1752012).sum := by decide
  have hdescent : baseEnd_1752012 < baseStart_1752012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752040 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1752040 : Nat := 118140960795 + 1752040 * 2 ^ 59
def prefixEnd_1752040 : Nat := 4983230072969 + 3 ^ 40 * 1752040 * 2
def baseEnd_1752040 : Nat := 599759097268953579428347

theorem tailTrace_1752040 : CollatzResearch.WordTrace tailWord_1752040 prefixEnd_1752040 599759097268953579428347 := by
  unfold tailWord_1752040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31951074286332889727310787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42601432381777186303081049 31951074286332889727310787)
  ·
    refine ⟨47926611429499334590966181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31951074286332889727310787 47926611429499334590966181)
    ·
      refine ⟨8986239643031125235806159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47926611429499334590966181 8986239643031125235806159)
      ·
        refine ⟨13479359464546687853709239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986239643031125235806159 13479359464546687853709239)
        ·
          refine ⟨20219039196820031780563859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479359464546687853709239 20219039196820031780563859)
          ·
            refine ⟨30328558795230047670845789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20219039196820031780563859 30328558795230047670845789)
            ·
              refine ⟨11373209548211267876567171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30328558795230047670845789 11373209548211267876567171)
              ·
                refine ⟨17059814322316901814850757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373209548211267876567171 17059814322316901814850757)
                ·
                  refine ⟨3198715185434419090284517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17059814322316901814850757 3198715185434419090284517)
                  ·
                    refine ⟨599759097268953579428347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3198715185434419090284517 599759097268953579428347)
                    ·
                      rfl

theorem cell22_1752040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1752040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752040 prefixEnd_1752040 := by exact prefixLift 1752040
  have htrace : WordTrace (prefixWord ++ tailWord_1752040) baseStart_1752040 baseEnd_1752040 := by
    simpa [prefixWord, tailWord_1752040, baseEnd_1752040] using wordTrace_append hprefix tailTrace_1752040
  have hstable : (prefixWord ++ tailWord_1752040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752040).length < 2 ^ (prefixWord ++ tailWord_1752040).sum := by decide
  have hdescent : baseEnd_1752040 < baseStart_1752040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752042 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1752042 : Nat := 118140960795 + 1752042 * 2 ^ 59
def prefixEnd_1752042 : Nat := 4983230072969 + 3 ^ 40 * 1752042 * 2
def baseEnd_1752042 : Nat := 599759781909826240878341

theorem tailTrace_1752042 : CollatzResearch.WordTrace tailWord_1752042 prefixEnd_1752042 599759781909826240878341 := by
  unfold tailWord_1752042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975555379664633449048595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42601481012439022530796253 15975555379664633449048595)
  ·
    refine ⟨23963333069496950173572893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15975555379664633449048595 23963333069496950173572893)
    ·
      refine ⟨8986249901061356315089835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23963333069496950173572893 8986249901061356315089835)
      ·
        refine ⟨13479374851592034472634753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986249901061356315089835 13479374851592034472634753)
        ·
          refine ⟨10109531138694025854476065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13479374851592034472634753 10109531138694025854476065)
          ·
            refine ⟨7582148354020519390857049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10109531138694025854476065 7582148354020519390857049)
            ·
              refine ⟨5686611265515389543142787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582148354020519390857049 5686611265515389543142787)
              ·
                refine ⟨8529916898273084314714181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686611265515389543142787 8529916898273084314714181)
                ·
                  refine ⟨1599359418426203309008909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8529916898273084314714181 1599359418426203309008909)
                  ·
                    refine ⟨599759781909826240878341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599359418426203309008909 599759781909826240878341)
                    ·
                      rfl

theorem cell22_1752042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1752042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752042 prefixEnd_1752042 := by exact prefixLift 1752042
  have htrace : WordTrace (prefixWord ++ tailWord_1752042) baseStart_1752042 baseEnd_1752042 := by
    simpa [prefixWord, tailWord_1752042, baseEnd_1752042] using wordTrace_append hprefix tailTrace_1752042
  have hstable : (prefixWord ++ tailWord_1752042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752042).length < 2 ^ (prefixWord ++ tailWord_1752042).sum := by decide
  have hdescent : baseEnd_1752042 < baseStart_1752042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752175 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_1752175 : Nat := 118140960795 + 1752175 * 2 ^ 59
def prefixEnd_1752175 : Nat := 4983230072969 + 3 ^ 40 * 1752175 * 2
def baseEnd_1752175 : Nat := 599805310527858227302933

theorem tailTrace_1752175 : CollatzResearch.WordTrace tailWord_1752175 prefixEnd_1752175 599805310527858227302933 := by
  unfold tailWord_1752175
  simp only [CollatzResearch.WordTrace]
  refine ⟨63907072427176697510785979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42604714951451131673857319 63907072427176697510785979)
  ·
    refine ⟨95860608640765046266178969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63907072427176697510785979 95860608640765046266178969)
    ·
      refine ⟨71895456480573784699634227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95860608640765046266178969 71895456480573784699634227)
      ·
        refine ⟨107843184720860677049451341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71895456480573784699634227 107843184720860677049451341)
        ·
          refine ⟨40441194270322753893544253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107843184720860677049451341 40441194270322753893544253)
          ·
            refine ⟨15165447851371032710079095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40441194270322753893544253 15165447851371032710079095)
            ·
              refine ⟨22748171777056549065118643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15165447851371032710079095 22748171777056549065118643)
              ·
                refine ⟨34122257665584823597677965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22748171777056549065118643 34122257665584823597677965)
                ·
                  refine ⟨12795846624594308849129237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34122257665584823597677965 12795846624594308849129237)
                  ·
                    refine ⟨599805310527858227302933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12795846624594308849129237 599805310527858227302933)
                    ·
                      rfl

theorem cell22_1752175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_1752175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752175 prefixEnd_1752175 := by exact prefixLift 1752175
  have htrace : WordTrace (prefixWord ++ tailWord_1752175) baseStart_1752175 baseEnd_1752175 := by
    simpa [prefixWord, tailWord_1752175, baseEnd_1752175] using wordTrace_append hprefix tailTrace_1752175
  have hstable : (prefixWord ++ tailWord_1752175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752175).length < 2 ^ (prefixWord ++ tailWord_1752175).sum := by decide
  have hdescent : baseEnd_1752175 < baseStart_1752175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752196 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1752196 : Nat := 118140960795 + 1752196 * 2 ^ 59
def prefixEnd_1752196 : Nat := 4983230072969 + 3 ^ 40 * 1752196 * 2
def baseEnd_1752196 : Nat := 199937499752340390842623

theorem tailTrace_1752196 : CollatzResearch.WordTrace tailWord_1752196 prefixEnd_1752196 199937499752340390842623 := by
  unfold tailWord_1752196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31953919180050309048650221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42605225573400412064866961 31953919180050309048650221)
  ·
    refine ⟨11982719692518865893243833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31953919180050309048650221 11982719692518865893243833)
    ·
      refine ⟨8987039769389149419932875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11982719692518865893243833 8987039769389149419932875)
      ·
        refine ⟨13480559654083724129899313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8987039769389149419932875 13480559654083724129899313)
        ·
          refine ⟨10110419740562793097424485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13480559654083724129899313 10110419740562793097424485)
          ·
            refine ⟨1895703701355523705767091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10110419740562793097424485 1895703701355523705767091)
            ·
              refine ⟨2843555552033285558650637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895703701355523705767091 2843555552033285558650637)
              ·
                refine ⟨1066333332012482084493989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843555552033285558650637 1066333332012482084493989)
                ·
                  refine ⟨199937499752340390842623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066333332012482084493989 199937499752340390842623)
                  ·
                    rfl

theorem cell22_1752196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1752196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752196 prefixEnd_1752196 := by exact prefixLift 1752196
  have htrace : WordTrace (prefixWord ++ tailWord_1752196) baseStart_1752196 baseEnd_1752196 := by
    simpa [prefixWord, tailWord_1752196, baseEnd_1752196] using wordTrace_append hprefix tailTrace_1752196
  have hstable : (prefixWord ++ tailWord_1752196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752196).length < 2 ^ (prefixWord ++ tailWord_1752196).sum := by decide
  have hdescent : baseEnd_1752196 < baseStart_1752196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752228 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_1752228 : Nat := 118140960795 + 1752228 * 2 ^ 59
def prefixEnd_1752228 : Nat := 4983230072969 + 3 ^ 40 * 1752228 * 2
def baseEnd_1752228 : Nat := 599823453510983755727771

theorem tailTrace_1752228 : CollatzResearch.WordTrace tailWord_1752228 prefixEnd_1752228 599823453510983755727771 := by
  unfold tailWord_1752228
  simp only [CollatzResearch.WordTrace]
  refine ⟨31954502747992343781232669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42606003663989791708310225 31954502747992343781232669)
  ·
    refine ⟨11982938530497128917962251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31954502747992343781232669 11982938530497128917962251)
    ·
      refine ⟨17974407795745693376943377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11982938530497128917962251 17974407795745693376943377)
      ·
        refine ⟨13480805846809270032707533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17974407795745693376943377 13480805846809270032707533)
        ·
          refine ⟨5055302192553476262265325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13480805846809270032707533 5055302192553476262265325)
          ·
            refine ⟨1895738322207553598349497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5055302192553476262265325 1895738322207553598349497)
            ·
              refine ⟨1421803741655665198762123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895738322207553598349497 1421803741655665198762123)
              ·
                refine ⟨2132705612483497798143185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421803741655665198762123 2132705612483497798143185)
                ·
                  refine ⟨1599529209362623348607389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132705612483497798143185 1599529209362623348607389)
                  ·
                    refine ⟨599823453510983755727771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599529209362623348607389 599823453510983755727771)
                    ·
                      rfl

theorem cell22_1752228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_1752228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752228 prefixEnd_1752228 := by exact prefixLift 1752228
  have htrace : WordTrace (prefixWord ++ tailWord_1752228) baseStart_1752228 baseEnd_1752228 := by
    simpa [prefixWord, tailWord_1752228, baseEnd_1752228] using wordTrace_append hprefix tailTrace_1752228
  have hstable : (prefixWord ++ tailWord_1752228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752228).length < 2 ^ (prefixWord ++ tailWord_1752228).sum := by decide
  have hdescent : baseEnd_1752228 < baseStart_1752228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752262 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1752262 : Nat := 118140960795 + 1752262 * 2 ^ 59
def prefixEnd_1752262 : Nat := 4983230072969 + 3 ^ 40 * 1752262 * 2
def baseEnd_1752262 : Nat := 599835092405819000377667

theorem tailTrace_1752262 : CollatzResearch.WordTrace tailWord_1752262 prefixEnd_1752262 599835092405819000377667 := by
  unfold tailWord_1752262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997195174308172230287595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42606830385241007579468693 1997195174308172230287595)
  ·
    refine ⟨2995792761462258345431393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997195174308172230287595 2995792761462258345431393)
    ·
      refine ⟨2246844571096693759073545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2995792761462258345431393 2246844571096693759073545)
      ·
        refine ⟨1685133428322520319305159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2246844571096693759073545 1685133428322520319305159)
        ·
          refine ⟨2527700142483780478957739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685133428322520319305159 2527700142483780478957739)
          ·
            refine ⟨3791550213725670718436609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527700142483780478957739 3791550213725670718436609)
            ·
              refine ⟨2843662660294253038827457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791550213725670718436609 2843662660294253038827457)
              ·
                refine ⟨2132746995220689779120593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843662660294253038827457 2132746995220689779120593)
                ·
                  refine ⟨1599560246415517334340445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132746995220689779120593 1599560246415517334340445)
                  ·
                    refine ⟨599835092405819000377667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599560246415517334340445 599835092405819000377667)
                    ·
                      rfl

theorem cell22_1752262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1752262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752262 prefixEnd_1752262 := by exact prefixLift 1752262
  have htrace : WordTrace (prefixWord ++ tailWord_1752262) baseStart_1752262 baseEnd_1752262 := by
    simpa [prefixWord, tailWord_1752262, baseEnd_1752262] using wordTrace_append hprefix tailTrace_1752262
  have hstable : (prefixWord ++ tailWord_1752262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752262).length < 2 ^ (prefixWord ++ tailWord_1752262).sum := by decide
  have hdescent : baseEnd_1752262 < baseStart_1752262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752316 : List Nat := [2, 2, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1752316 : Nat := 118140960795 + 1752316 * 2 ^ 59
def prefixEnd_1752316 : Nat := 4983230072969 + 3 ^ 40 * 1752316 * 2
def baseEnd_1752316 : Nat := 599853577709380859527501

theorem tailTrace_1752316 : CollatzResearch.WordTrace tailWord_1752316 prefixEnd_1752316 599853577709380859527501 := by
  unfold tailWord_1752316
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956107559832939295834401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42608143413110585727779201 31956107559832939295834401)
  ·
    refine ⟨23967080669874704471875801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31956107559832939295834401 23967080669874704471875801)
    ·
      refine ⟨17975310502406028353906851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23967080669874704471875801 17975310502406028353906851)
      ·
        refine ⟨26962965753609042530860277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975310502406028353906851 26962965753609042530860277)
        ·
          refine ⟨2527778039400847737268151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26962965753609042530860277 2527778039400847737268151)
          ·
            refine ⟨3791667059101271605902227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527778039400847737268151 3791667059101271605902227)
            ·
              refine ⟨5687500588651907408853341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791667059101271605902227 5687500588651907408853341)
              ·
                refine ⟨2132812720744465278320003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5687500588651907408853341 2132812720744465278320003)
                ·
                  refine ⟨3199219081116697917480005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132812720744465278320003 3199219081116697917480005)
                  ·
                    refine ⟨599853577709380859527501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199219081116697917480005 599853577709380859527501)
                    ·
                      rfl

theorem cell22_1752316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1752316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752316 prefixEnd_1752316 := by exact prefixLift 1752316
  have htrace : WordTrace (prefixWord ++ tailWord_1752316) baseStart_1752316 baseEnd_1752316 := by
    simpa [prefixWord, tailWord_1752316, baseEnd_1752316] using wordTrace_append hprefix tailTrace_1752316
  have hstable : (prefixWord ++ tailWord_1752316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752316).length < 2 ^ (prefixWord ++ tailWord_1752316).sum := by decide
  have hdescent : baseEnd_1752316 < baseStart_1752316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752329 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 4, 3]
def baseStart_1752329 : Nat := 118140960795 + 1752329 * 2 ^ 59
def prefixEnd_1752329 : Nat := 4983230072969 + 3 ^ 40 * 1752329 * 2
def baseEnd_1752329 : Nat := 599858027875053158952461

theorem tailTrace_1752329 : CollatzResearch.WordTrace tailWord_1752329 prefixEnd_1752329 599858027875053158952461 := by
  unfold tailWord_1752329
  simp only [CollatzResearch.WordTrace]
  refine ⟨63912689268618781811892041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42608459512412521207928027 63912689268618781811892041)
  ·
    refine ⟨47934516951464086358919031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63912689268618781811892041 47934516951464086358919031)
    ·
      refine ⟨71901775427196129538378547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47934516951464086358919031 71901775427196129538378547)
      ·
        refine ⟨107852663140794194307567821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71901775427196129538378547 107852663140794194307567821)
        ·
          refine ⟨40444748677797822865337933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107852663140794194307567821 40444748677797822865337933)
          ·
            refine ⟨15166780754174183574501725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40444748677797822865337933 15166780754174183574501725)
            ·
              refine ⟨5687542782815318840438147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15166780754174183574501725 5687542782815318840438147)
              ·
                refine ⟨8531314174222978260657221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687542782815318840438147 8531314174222978260657221)
                ·
                  refine ⟨1599621407666808423873229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8531314174222978260657221 1599621407666808423873229)
                  ·
                    refine ⟨599858027875053158952461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599621407666808423873229 599858027875053158952461)
                    ·
                      rfl

theorem cell22_1752329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 3].length) (baseStart_1752329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752329 prefixEnd_1752329 := by exact prefixLift 1752329
  have htrace : WordTrace (prefixWord ++ tailWord_1752329) baseStart_1752329 baseEnd_1752329 := by
    simpa [prefixWord, tailWord_1752329, baseEnd_1752329] using wordTrace_append hprefix tailTrace_1752329
  have hstable : (prefixWord ++ tailWord_1752329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752329).length < 2 ^ (prefixWord ++ tailWord_1752329).sum := by decide
  have hdescent : baseEnd_1752329 < baseStart_1752329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752346 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1752346 : Nat := 118140960795 + 1752346 * 2 ^ 59
def prefixEnd_1752346 : Nat := 4983230072969 + 3 ^ 40 * 1752346 * 2
def baseEnd_1752346 : Nat := 599863847322470781277409

theorem tailTrace_1752346 : CollatzResearch.WordTrace tailWord_1752346 prefixEnd_1752346 599863847322470781277409 := by
  unfold tailWord_1752346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978327327389298428815223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42608872873038129143507261 15978327327389298428815223)
  ·
    refine ⟨23967490991083947643222835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15978327327389298428815223 23967490991083947643222835)
    ·
      refine ⟨35951236486625921464834253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23967490991083947643222835 35951236486625921464834253)
      ·
        refine ⟨13481713682484720549312845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35951236486625921464834253 13481713682484720549312845)
        ·
          refine ⟨5055642630931770205992317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13481713682484720549312845 5055642630931770205992317)
          ·
            refine ⟨1895865986599413827247119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5055642630931770205992317 1895865986599413827247119)
            ·
              refine ⟨2843798979899120740870679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895865986599413827247119 2843798979899120740870679)
              ·
                refine ⟨4265698469848681111306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843798979899120740870679 4265698469848681111306019)
                ·
                  refine ⟨6398547704773021666959029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265698469848681111306019 6398547704773021666959029)
                  ·
                    refine ⟨599863847322470781277409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6398547704773021666959029 599863847322470781277409)
                    ·
                      rfl

theorem cell22_1752346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1752346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752346 prefixEnd_1752346 := by exact prefixLift 1752346
  have htrace : WordTrace (prefixWord ++ tailWord_1752346) baseStart_1752346 baseEnd_1752346 := by
    simpa [prefixWord, tailWord_1752346, baseEnd_1752346] using wordTrace_append hprefix tailTrace_1752346
  have hstable : (prefixWord ++ tailWord_1752346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752346).length < 2 ^ (prefixWord ++ tailWord_1752346).sum := by decide
  have hdescent : baseEnd_1752346 < baseStart_1752346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752350 : List Nat := [4, 3, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1752350 : Nat := 118140960795 + 1752350 * 2 ^ 59
def prefixEnd_1752350 : Nat := 4983230072969 + 3 ^ 40 * 1752350 * 2
def baseEnd_1752350 : Nat := 599865216604216104177397

theorem tailTrace_1752350 : CollatzResearch.WordTrace tailWord_1752350 prefixEnd_1752350 599865216604216104177397 := by
  unfold tailWord_1752350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7989181900192837799800813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42608970134361801598937669 7989181900192837799800813)
  ·
    refine ⟨2995943212572314174925305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7989181900192837799800813 2995943212572314174925305)
    ·
      refine ⟨2246957409429235631193979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2995943212572314174925305 2246957409429235631193979)
      ·
        refine ⟨3370436114143853446790969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246957409429235631193979 3370436114143853446790969)
        ·
          refine ⟨2527827085607890085093227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3370436114143853446790969 2527827085607890085093227)
          ·
            refine ⟨3791740628411835127639841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527827085607890085093227 3791740628411835127639841)
            ·
              refine ⟨2843805471308876345729881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791740628411835127639841 2843805471308876345729881)
              ·
                refine ⟨2132854103481657259297411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843805471308876345729881 2132854103481657259297411)
                ·
                  refine ⟨3199281155222485888946117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132854103481657259297411 3199281155222485888946117)
                  ·
                    refine ⟨599865216604216104177397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199281155222485888946117 599865216604216104177397)
                    ·
                      rfl

theorem cell22_1752350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1752350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752350 prefixEnd_1752350 := by exact prefixLift 1752350
  have htrace : WordTrace (prefixWord ++ tailWord_1752350) baseStart_1752350 baseEnd_1752350 := by
    simpa [prefixWord, tailWord_1752350, baseEnd_1752350] using wordTrace_append hprefix tailTrace_1752350
  have hstable : (prefixWord ++ tailWord_1752350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752350).length < 2 ^ (prefixWord ++ tailWord_1752350).sum := by decide
  have hdescent : baseEnd_1752350 < baseStart_1752350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752365 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 4]
def baseStart_1752365 : Nat := 118140960795 + 1752365 * 2 ^ 59
def prefixEnd_1752365 : Nat := 4983230072969 + 3 ^ 40 * 1752365 * 2
def baseEnd_1752365 : Nat := 199956783803587021684117

theorem tailTrace_1752365 : CollatzResearch.WordTrace tailWord_1752365 prefixEnd_1752365 199956783803587021684117 := by
  unfold tailWord_1752365
  simp only [CollatzResearch.WordTrace]
  refine ⟨63914002296488359960202549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42609334864325573306801699 63914002296488359960202549)
  ·
    refine ⟨5991937715295783746268989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63914002296488359960202549 5991937715295783746268989)
    ·
      refine ⟨2246976643235918904850871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5991937715295783746268989 2246976643235918904850871)
      ·
        refine ⟨3370464964853878357276307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246976643235918904850871 3370464964853878357276307)
        ·
          refine ⟨5055697447280817535914461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370464964853878357276307 5055697447280817535914461)
          ·
            refine ⟨1895886542730306575967923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5055697447280817535914461 1895886542730306575967923)
            ·
              refine ⟨2843829814095459863951885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895886542730306575967923 2843829814095459863951885)
              ·
                refine ⟨1066436180285797448981957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843829814095459863951885 1066436180285797448981957)
                ·
                  refine ⟨199956783803587021684117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066436180285797448981957 199956783803587021684117)
                  ·
                    rfl

theorem cell22_1752365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_1752365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752365 prefixEnd_1752365 := by exact prefixLift 1752365
  have htrace : WordTrace (prefixWord ++ tailWord_1752365) baseStart_1752365 baseEnd_1752365 := by
    simpa [prefixWord, tailWord_1752365, baseEnd_1752365] using wordTrace_append hprefix tailTrace_1752365
  have hstable : (prefixWord ++ tailWord_1752365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752365).length < 2 ^ (prefixWord ++ tailWord_1752365).sum := by decide
  have hdescent : baseEnd_1752365 < baseStart_1752365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752391 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1752391 : Nat := 118140960795 + 1752391 * 2 ^ 59
def prefixEnd_1752391 : Nat := 4983230072969 + 3 ^ 40 * 1752391 * 2
def baseEnd_1752391 : Nat := 599879251742105663902271

theorem tailTrace_1752391 : CollatzResearch.WordTrace tailWord_1752391 prefixEnd_1752391 599879251742105663902271 := by
  unfold tailWord_1752391
  simp only [CollatzResearch.WordTrace]
  refine ⟨63914950594394166400649027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42609967062929444267099351 63914950594394166400649027)
  ·
    refine ⟨95872425891591249600973541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63914950594394166400649027 95872425891591249600973541)
    ·
      refine ⟨17976079854673359300182539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95872425891591249600973541 17976079854673359300182539)
      ·
        refine ⟨26964119782010038950273809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17976079854673359300182539 26964119782010038950273809)
        ·
          refine ⟨20223089836507529212705357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26964119782010038950273809 20223089836507529212705357)
          ·
            refine ⟨7583658688690323454764509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20223089836507529212705357 7583658688690323454764509)
            ·
              refine ⟨2843872008258871295536691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583658688690323454764509 2843872008258871295536691)
              ·
                refine ⟨4265808012388306943305037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843872008258871295536691 4265808012388306943305037)
                ·
                  refine ⟨1599678004645615103739389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4265808012388306943305037 1599678004645615103739389)
                  ·
                    refine ⟨599879251742105663902271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1599678004645615103739389 599879251742105663902271)
                    ·
                      rfl

theorem cell22_1752391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1752391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752391 prefixEnd_1752391 := by exact prefixLift 1752391
  have htrace : WordTrace (prefixWord ++ tailWord_1752391) baseStart_1752391 baseEnd_1752391 := by
    simpa [prefixWord, tailWord_1752391, baseEnd_1752391] using wordTrace_append hprefix tailTrace_1752391
  have hstable : (prefixWord ++ tailWord_1752391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752391).length < 2 ^ (prefixWord ++ tailWord_1752391).sum := by decide
  have hdescent : baseEnd_1752391 < baseStart_1752391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752569 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1752569 : Nat := 118140960795 + 1752569 * 2 ^ 59
def prefixEnd_1752569 : Nat := 4983230072969 + 3 ^ 40 * 1752569 * 2
def baseEnd_1752569 : Nat := 599940184779772532951725

theorem tailTrace_1752569 : CollatzResearch.WordTrace tailWord_1752569 prefixEnd_1752569 599940184779772532951725 := by
  unfold tailWord_1752569
  simp only [CollatzResearch.WordTrace]
  refine ⟨63921442787749302800628761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42614295191832868533752507 63921442787749302800628761)
  ·
    refine ⟨47941082090811977100471571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63921442787749302800628761 47941082090811977100471571)
    ·
      refine ⟨71911623136217965650707357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47941082090811977100471571 71911623136217965650707357)
      ·
        refine ⟨26966858676081737119015259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71911623136217965650707357 26966858676081737119015259)
        ·
          refine ⟨40450288014122605678522889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26966858676081737119015259 40450288014122605678522889)
          ·
            refine ⟨30337716010591954258892167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40450288014122605678522889 30337716010591954258892167)
            ·
              refine ⟨45506574015887931388338251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30337716010591954258892167 45506574015887931388338251)
              ·
                refine ⟨68259861023831897082507377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45506574015887931388338251 68259861023831897082507377)
                ·
                  refine ⟨51194895767873922811880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68259861023831897082507377 51194895767873922811880533)
                  ·
                    refine ⟨599940184779772532951725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51194895767873922811880533 599940184779772532951725)
                    ·
                      rfl

theorem cell22_1752569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1752569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752569 prefixEnd_1752569 := by exact prefixLift 1752569
  have htrace : WordTrace (prefixWord ++ tailWord_1752569) baseStart_1752569 baseEnd_1752569 := by
    simpa [prefixWord, tailWord_1752569, baseEnd_1752569] using wordTrace_append hprefix tailTrace_1752569
  have hstable : (prefixWord ++ tailWord_1752569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752569).length < 2 ^ (prefixWord ++ tailWord_1752569).sum := by decide
  have hdescent : baseEnd_1752569 < baseStart_1752569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752573 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 5]
def baseStart_1752573 : Nat := 118140960795 + 1752573 * 2 ^ 59
def prefixEnd_1752573 : Nat := 4983230072969 + 3 ^ 40 * 1752573 * 2
def baseEnd_1752573 : Nat := 199980518020505951950571

theorem tailTrace_1752573 : CollatzResearch.WordTrace tailWord_1752573 prefixEnd_1752573 199980518020505951950571 := by
  unfold tailWord_1752573
  simp only [CollatzResearch.WordTrace]
  refine ⟨63921588679734811483774373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42614392453156540989182915 63921588679734811483774373)
  ·
    refine ⟨11985297877450277153207695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63921588679734811483774373 11985297877450277153207695)
    ·
      refine ⟨17977946816175415729811543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11985297877450277153207695 17977946816175415729811543)
      ·
        refine ⟨26966920224263123594717315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17977946816175415729811543 26966920224263123594717315)
        ·
          refine ⟨40450380336394685392075973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26966920224263123594717315 40450380336394685392075973)
          ·
            refine ⟨7584446313074003511014245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40450380336394685392075973 7584446313074003511014245)
            ·
              refine ⟨1422083683701375658315171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7584446313074003511014245 1422083683701375658315171)
              ·
                refine ⟨2133125525552063487472757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422083683701375658315171 2133125525552063487472757)
                ·
                  refine ⟨199980518020505951950571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133125525552063487472757 199980518020505951950571)
                  ·
                    rfl

theorem cell22_1752573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_1752573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752573 prefixEnd_1752573 := by exact prefixLift 1752573
  have htrace : WordTrace (prefixWord ++ tailWord_1752573) baseStart_1752573 baseEnd_1752573 := by
    simpa [prefixWord, tailWord_1752573, baseEnd_1752573] using wordTrace_append hprefix tailTrace_1752573
  have hstable : (prefixWord ++ tailWord_1752573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752573).length < 2 ^ (prefixWord ++ tailWord_1752573).sum := by decide
  have hdescent : baseEnd_1752573 < baseStart_1752573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752633 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_1752633 : Nat := 118140960795 + 1752633 * 2 ^ 59
def prefixEnd_1752633 : Nat := 4983230072969 + 3 ^ 40 * 1752633 * 2
def baseEnd_1752633 : Nat := 599962093287697699351529

theorem tailTrace_1752633 : CollatzResearch.WordTrace tailWord_1752633 prefixEnd_1752633 599962093287697699351529 := by
  unfold tailWord_1752633
  simp only [CollatzResearch.WordTrace]
  refine ⟨63923777059517441730958553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42615851373011627820639035 63923777059517441730958553)
  ·
    refine ⟨47942832794638081298218915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63923777059517441730958553 47942832794638081298218915)
    ·
      refine ⟨71914249191957121947328373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47942832794638081298218915 71914249191957121947328373)
      ·
        refine ⟨6741960861745980182562035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71914249191957121947328373 6741960861745980182562035)
        ·
          refine ⟨10112941292618970273843053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741960861745980182562035 10112941292618970273843053)
          ·
            refine ⟨3792352984732113852691145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10112941292618970273843053 3792352984732113852691145)
            ·
              refine ⟨2844264738549085389518359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792352984732113852691145 2844264738549085389518359)
              ·
                refine ⟨4266397107823628084277539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844264738549085389518359 4266397107823628084277539)
                ·
                  refine ⟨6399595661735442126416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266397107823628084277539 6399595661735442126416309)
                  ·
                    refine ⟨599962093287697699351529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6399595661735442126416309 599962093287697699351529)
                    ·
                      rfl

theorem cell22_1752633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_1752633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752633 prefixEnd_1752633 := by exact prefixLift 1752633
  have htrace : WordTrace (prefixWord ++ tailWord_1752633) baseStart_1752633 baseEnd_1752633 := by
    simpa [prefixWord, tailWord_1752633, baseEnd_1752633] using wordTrace_append hprefix tailTrace_1752633
  have hstable : (prefixWord ++ tailWord_1752633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752633).length < 2 ^ (prefixWord ++ tailWord_1752633).sum := by decide
  have hdescent : baseEnd_1752633 < baseStart_1752633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752768 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_1752768 : Nat := 118140960795 + 1752768 * 2 ^ 59
def prefixEnd_1752768 : Nat := 4983230072969 + 3 ^ 40 * 1752768 * 2
def baseEnd_1752768 : Nat := 600008306546602347226115

theorem tailTrace_1752768 : CollatzResearch.WordTrace tailWord_1752768 prefixEnd_1752768 600008306546602347226115 := by
  unfold tailWord_1752768
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964350457014179893561479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42619133942685573191415305 31964350457014179893561479)
  ·
    refine ⟨47946525685521269840342219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31964350457014179893561479 47946525685521269840342219)
    ·
      refine ⟨71919788528281904760513329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47946525685521269840342219 71919788528281904760513329)
      ·
        refine ⟨53939841396211428570384997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71919788528281904760513329 53939841396211428570384997)
        ·
          refine ⟨10113720261789642856947187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53939841396211428570384997 10113720261789642856947187)
          ·
            refine ⟨15170580392684464285420781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10113720261789642856947187 15170580392684464285420781)
            ·
              refine ⟨5688967647256674107032793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15170580392684464285420781 5688967647256674107032793)
              ·
                refine ⟨4266725735442505580274595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688967647256674107032793 4266725735442505580274595)
                ·
                  refine ⟨6400088603163758370411893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266725735442505580274595 6400088603163758370411893)
                  ·
                    refine ⟨600008306546602347226115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6400088603163758370411893 600008306546602347226115)
                    ·
                      rfl

theorem cell22_1752768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_1752768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752768 prefixEnd_1752768 := by exact prefixLift 1752768
  have htrace : WordTrace (prefixWord ++ tailWord_1752768) baseStart_1752768 baseEnd_1752768 := by
    simpa [prefixWord, tailWord_1752768, baseEnd_1752768] using wordTrace_append hprefix tailTrace_1752768
  have hstable : (prefixWord ++ tailWord_1752768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752768).length < 2 ^ (prefixWord ++ tailWord_1752768).sum := by decide
  have hdescent : baseEnd_1752768 < baseStart_1752768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752772 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1752772 : Nat := 118140960795 + 1752772 * 2 ^ 59
def prefixEnd_1752772 : Nat := 4983230072969 + 3 ^ 40 * 1752772 * 2
def baseEnd_1752772 : Nat := 600009675828347670126103

theorem tailTrace_1752772 : CollatzResearch.WordTrace tailWord_1752772 prefixEnd_1752772 600009675828347670126103 := by
  unfold tailWord_1752772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964423403006934235134285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42619231204009245646845713 31964423403006934235134285)
  ·
    refine ⟨11986658776127600338175357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31964423403006934235134285 11986658776127600338175357)
    ·
      refine ⟨4494997041047850126815759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11986658776127600338175357 4494997041047850126815759)
      ·
        refine ⟨6742495561571775190223639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494997041047850126815759 6742495561571775190223639)
        ·
          refine ⟨10113743342357662785335459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742495561571775190223639 10113743342357662785335459)
          ·
            refine ⟨15170615013536494178003189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10113743342357662785335459 15170615013536494178003189)
            ·
              refine ⟨1422245157519046329187799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15170615013536494178003189 1422245157519046329187799)
              ·
                refine ⟨2133367736278569493781699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422245157519046329187799 2133367736278569493781699)
                ·
                  refine ⟨3200051604417854240672549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133367736278569493781699 3200051604417854240672549)
                  ·
                    refine ⟨600009675828347670126103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200051604417854240672549 600009675828347670126103)
                    ·
                      rfl

theorem cell22_1752772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1752772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752772 prefixEnd_1752772 := by exact prefixLift 1752772
  have htrace : WordTrace (prefixWord ++ tailWord_1752772) baseStart_1752772 baseEnd_1752772 := by
    simpa [prefixWord, tailWord_1752772, baseEnd_1752772] using wordTrace_append hprefix tailTrace_1752772
  have hstable : (prefixWord ++ tailWord_1752772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752772).length < 2 ^ (prefixWord ++ tailWord_1752772).sum := by decide
  have hdescent : baseEnd_1752772 < baseStart_1752772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752785 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 2, 3]
def baseStart_1752785 : Nat := 118140960795 + 1752785 * 2 ^ 59
def prefixEnd_1752785 : Nat := 4983230072969 + 3 ^ 40 * 1752785 * 2
def baseEnd_1752785 : Nat := 600014125994019969551063

theorem tailTrace_1752785 : CollatzResearch.WordTrace tailWord_1752785 prefixEnd_1752785 600014125994019969551063 := by
  unfold tailWord_1752785
  simp only [CollatzResearch.WordTrace]
  refine ⟨63929320954966771690491809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42619547303311181126994539 63929320954966771690491809)
  ·
    refine ⟨47946990716225078767868857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63929320954966771690491809 47946990716225078767868857)
    ·
      refine ⟨35960243037168809075901643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47946990716225078767868857 35960243037168809075901643)
      ·
        refine ⟨53940364555753213613852465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35960243037168809075901643 53940364555753213613852465)
        ·
          refine ⟨40455273416814910210389349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53940364555753213613852465 40455273416814910210389349)
          ·
            refine ⟨7585363765652795664448003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40455273416814910210389349 7585363765652795664448003)
            ·
              refine ⟨11378045648479193496672005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585363765652795664448003 11378045648479193496672005)
              ·
                refine ⟨2133383559089848780626001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11378045648479193496672005 2133383559089848780626001)
                ·
                  refine ⟨1600037669317386585469501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2133383559089848780626001 1600037669317386585469501)
                  ·
                    refine ⟨600014125994019969551063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1600037669317386585469501 600014125994019969551063)
                    ·
                      rfl

theorem cell22_1752785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_1752785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752785 prefixEnd_1752785 := by exact prefixLift 1752785
  have htrace : WordTrace (prefixWord ++ tailWord_1752785) baseStart_1752785 baseEnd_1752785 := by
    simpa [prefixWord, tailWord_1752785, baseEnd_1752785] using wordTrace_append hprefix tailTrace_1752785
  have hstable : (prefixWord ++ tailWord_1752785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752785).length < 2 ^ (prefixWord ++ tailWord_1752785).sum := by decide
  have hdescent : baseEnd_1752785 < baseStart_1752785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752838 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1752838 : Nat := 118140960795 + 1752838 * 2 ^ 59
def prefixEnd_1752838 : Nat := 4983230072969 + 3 ^ 40 * 1752838 * 2
def baseEnd_1752838 : Nat := 200010756325715165991967

theorem tailTrace_1752838 : CollatzResearch.WordTrace tailWord_1752838 prefixEnd_1752838 200010756325715165991967 := by
  unfold tailWord_1752838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997851688242961304442849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42620836015849841161447445 1997851688242961304442849)
  ·
    refine ⟨1498388766182220978332137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1997851688242961304442849 1498388766182220978332137)
    ·
      refine ⟨1123791574636665733749103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1498388766182220978332137 1123791574636665733749103)
      ·
        refine ⟨1685687361954998600623655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123791574636665733749103 1685687361954998600623655)
        ·
          refine ⟨2528531042932497900935483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685687361954998600623655 2528531042932497900935483)
          ·
            refine ⟨3792796564398746851403225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528531042932497900935483 3792796564398746851403225)
            ·
              refine ⟨2844597423299060138552419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792796564398746851403225 2844597423299060138552419)
              ·
                refine ⟨4266896134948590207828629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844597423299060138552419 4266896134948590207828629)
                ·
                  refine ⟨200010756325715165991967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4266896134948590207828629 200010756325715165991967)
                  ·
                    rfl

theorem cell22_1752838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1752838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752838 prefixEnd_1752838 := by exact prefixLift 1752838
  have htrace : WordTrace (prefixWord ++ tailWord_1752838) baseStart_1752838 baseEnd_1752838 := by
    simpa [prefixWord, tailWord_1752838, baseEnd_1752838] using wordTrace_append hprefix tailTrace_1752838
  have hstable : (prefixWord ++ tailWord_1752838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752838).length < 2 ^ (prefixWord ++ tailWord_1752838).sum := by decide
  have hdescent : baseEnd_1752838 < baseStart_1752838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752950 : List Nat := [5, 1, 1, 3, 12]
def baseStart_1752950 : Nat := 118140960795 + 1752950 * 2 ^ 59
def prefixEnd_1752950 : Nat := 4983230072969 + 3 ^ 40 * 1752950 * 2
def baseEnd_1752950 : Nat := 2469426373934216210599

theorem tailTrace_1752950 : CollatzResearch.WordTrace tailWord_1752950 prefixEnd_1752950 2469426373934216210599 := by
  unfold tailWord_1752950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995958687460562804390519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42623559332912669913498869 3995958687460562804390519)
  ·
    refine ⟨5993938031190844206585779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995958687460562804390519 5993938031190844206585779)
    ·
      refine ⟨8990907046786266309878669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993938031190844206585779 8990907046786266309878669)
      ·
        refine ⟨3371590142544849866204501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8990907046786266309878669 3371590142544849866204501)
        ·
          refine ⟨2469426373934216210599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3371590142544849866204501 2469426373934216210599)
          ·
            rfl

theorem cell22_1752950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 12].length) (baseStart_1752950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752950 prefixEnd_1752950 := by exact prefixLift 1752950
  have htrace : WordTrace (prefixWord ++ tailWord_1752950) baseStart_1752950 baseEnd_1752950 := by
    simpa [prefixWord, tailWord_1752950, baseEnd_1752950] using wordTrace_append hprefix tailTrace_1752950
  have hstable : (prefixWord ++ tailWord_1752950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752950).length < 2 ^ (prefixWord ++ tailWord_1752950).sum := by decide
  have hdescent : baseEnd_1752950 < baseStart_1752950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752967 : List Nat := [1, 1, 4, 2, 4, 2, 1, 7]
def baseStart_1752967 : Nat := 118140960795 + 1752967 * 2 ^ 59
def prefixEnd_1752967 : Nat := 4983230072969 + 3 ^ 40 * 1752967 * 2
def baseEnd_1752967 : Nat := 66675158701492462388945

theorem tailTrace_1752967 : CollatzResearch.WordTrace tailWord_1752967 prefixEnd_1752967 66675158701492462388945 := by
  unfold tailWord_1752967
  simp only [CollatzResearch.WordTrace]
  refine ⟨63935959040307416773617155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42623972693538277849078103 63935959040307416773617155)
  ·
    refine ⟨95903938560461125160425733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63935959040307416773617155 95903938560461125160425733)
    ·
      refine ⟨17981988480086460967579825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95903938560461125160425733 17981988480086460967579825)
      ·
        refine ⟨13486491360064845725684869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17981988480086460967579825 13486491360064845725684869)
        ·
          refine ⟨2528717130012158573565913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13486491360064845725684869 2528717130012158573565913)
          ·
            refine ⟨1896537847509118930174435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528717130012158573565913 1896537847509118930174435)
            ·
              refine ⟨2844806771263678395261653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896537847509118930174435 2844806771263678395261653)
              ·
                refine ⟨66675158701492462388945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2844806771263678395261653 66675158701492462388945)
                ·
                  rfl

theorem cell22_1752967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 7].length) (baseStart_1752967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752967 prefixEnd_1752967 := by exact prefixLift 1752967
  have htrace : WordTrace (prefixWord ++ tailWord_1752967) baseStart_1752967 baseEnd_1752967 := by
    simpa [prefixWord, tailWord_1752967, baseEnd_1752967] using wordTrace_append hprefix tailTrace_1752967
  have hstable : (prefixWord ++ tailWord_1752967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752967).length < 2 ^ (prefixWord ++ tailWord_1752967).sum := by decide
  have hdescent : baseEnd_1752967 < baseStart_1752967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752984 : List Nat := [2, 1, 2, 6, 1, 1, 3, 6]
def baseStart_1752984 : Nat := 118140960795 + 1752984 * 2 ^ 59
def prefixEnd_1752984 : Nat := 4983230072969 + 3 ^ 40 * 1752984 * 2
def baseEnd_1752984 : Nat := 66675805306761087091717

theorem tailTrace_1752984 : CollatzResearch.WordTrace tailWord_1752984 prefixEnd_1752984 66675805306761087091717 := by
  unfold tailWord_1752984
  simp only [CollatzResearch.WordTrace]
  refine ⟨31968289540622914338493003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42624386054163885784657337 31968289540622914338493003)
  ·
    refine ⟨47952434310934371507739505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31968289540622914338493003 47952434310934371507739505)
    ·
      refine ⟨35964325733200778630804629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47952434310934371507739505 35964325733200778630804629)
      ·
        refine ⟨1685827768743786498318967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35964325733200778630804629 1685827768743786498318967)
        ·
          refine ⟨2528741653115679747478451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685827768743786498318967 2528741653115679747478451)
          ·
            refine ⟨3793112479673519621217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528741653115679747478451 3793112479673519621217677)
            ·
              refine ⟨1422417179877569857956629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3793112479673519621217677 1422417179877569857956629)
              ·
                refine ⟨66675805306761087091717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1422417179877569857956629 66675805306761087091717)
                ·
                  rfl

theorem cell22_1752984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_1752984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1752984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1752984 prefixEnd_1752984 := by exact prefixLift 1752984
  have htrace : WordTrace (prefixWord ++ tailWord_1752984) baseStart_1752984 baseEnd_1752984 := by
    simpa [prefixWord, tailWord_1752984, baseEnd_1752984] using wordTrace_append hprefix tailTrace_1752984
  have hstable : (prefixWord ++ tailWord_1752984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752984).length < 2 ^ (prefixWord ++ tailWord_1752984).sum := by decide
  have hdescent : baseEnd_1752984 < baseStart_1752984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753040 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_1753040 : Nat := 118140960795 + 1753040 * 2 ^ 59
def prefixEnd_1753040 : Nat := 4983230072969 + 3 ^ 40 * 1753040 * 2
def baseEnd_1753040 : Nat := 200033805901761434808427

theorem tailTrace_1753040 : CollatzResearch.WordTrace tailWord_1753040 prefixEnd_1753040 200033805901761434808427 := by
  unfold tailWord_1753040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31969310784521475120512287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42625747712695300160683049 31969310784521475120512287)
  ·
    refine ⟨47953966176782212680768431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31969310784521475120512287 47953966176782212680768431)
    ·
      refine ⟨71930949265173319021152647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47953966176782212680768431 71930949265173319021152647)
      ·
        refine ⟨107896423897759978531728971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71930949265173319021152647 107896423897759978531728971)
        ·
          refine ⟨161844635846639967797593457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107896423897759978531728971 161844635846639967797593457)
          ·
            refine ⟨121383476884979975848195093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161844635846639967797593457 121383476884979975848195093)
            ·
              refine ⟨5689850478983436367884145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121383476884979975848195093 5689850478983436367884145)
              ·
                refine ⟨4267387859237577275913109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5689850478983436367884145 4267387859237577275913109)
                ·
                  refine ⟨200033805901761434808427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4267387859237577275913109 200033805901761434808427)
                  ·
                    rfl

theorem cell22_1753040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_1753040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753040 prefixEnd_1753040 := by exact prefixLift 1753040
  have htrace : WordTrace (prefixWord ++ tailWord_1753040) baseStart_1753040 baseEnd_1753040 := by
    simpa [prefixWord, tailWord_1753040, baseEnd_1753040] using wordTrace_append hprefix tailTrace_1753040
  have hstable : (prefixWord ++ tailWord_1753040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753040).length < 2 ^ (prefixWord ++ tailWord_1753040).sum := by decide
  have hdescent : baseEnd_1753040 < baseStart_1753040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753072 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_1753072 : Nat := 118140960795 + 1753072 * 2 ^ 59
def prefixEnd_1753072 : Nat := 4983230072969 + 3 ^ 40 * 1753072 * 2
def baseEnd_1753072 : Nat := 600112371959246887625183

theorem tailTrace_1753072 : CollatzResearch.WordTrace tailWord_1753072 prefixEnd_1753072 600112371959246887625183 := by
  unfold tailWord_1753072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31969894352463509853094735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42626525803284679804126313 31969894352463509853094735)
  ·
    refine ⟨47954841528695264779642103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31969894352463509853094735 47954841528695264779642103)
    ·
      refine ⟨71932262293042897169463155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47954841528695264779642103 71932262293042897169463155)
      ·
        refine ⟨107898393439564345754194733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71932262293042897169463155 107898393439564345754194733)
        ·
          refine ⟨40461897539836629657823025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107898393439564345754194733 40461897539836629657823025)
          ·
            refine ⟨30346423154877472243367269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40461897539836629657823025 30346423154877472243367269)
            ·
              refine ⟨5689954341539526045631363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30346423154877472243367269 5689954341539526045631363)
              ·
                refine ⟨8534931512309289068447045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689954341539526045631363 8534931512309289068447045)
                ·
                  refine ⟨1600299658557991700333821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8534931512309289068447045 1600299658557991700333821)
                  ·
                    refine ⟨600112371959246887625183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1600299658557991700333821 600112371959246887625183)
                    ·
                      rfl

theorem cell22_1753072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_1753072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753072 prefixEnd_1753072 := by exact prefixLift 1753072
  have htrace : WordTrace (prefixWord ++ tailWord_1753072) baseStart_1753072 baseEnd_1753072 := by
    simpa [prefixWord, tailWord_1753072, baseEnd_1753072] using wordTrace_append hprefix tailTrace_1753072
  have hstable : (prefixWord ++ tailWord_1753072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753072).length < 2 ^ (prefixWord ++ tailWord_1753072).sum := by decide
  have hdescent : baseEnd_1753072 < baseStart_1753072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753085 : List Nat := [1, 4, 1, 1, 1, 2, 3, 9]
def baseStart_1753085 : Nat := 118140960795 + 1753085 * 2 ^ 59
def prefixEnd_1753085 : Nat := 4983230072969 + 3 ^ 40 * 1753085 * 2
def baseEnd_1753085 : Nat := 66679646902768798561127

theorem tailTrace_1753085 : CollatzResearch.WordTrace tailWord_1753085 prefixEnd_1753085 66679646902768798561127 := by
  unfold tailWord_1753085
  simp only [CollatzResearch.WordTrace]
  refine ⟨63940262853879922926412709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42626841902586615284275139 63940262853879922926412709)
  ·
    refine ⟨11988799285102485548702383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63940262853879922926412709 11988799285102485548702383)
    ·
      refine ⟨17983198927653728323053575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11988799285102485548702383 17983198927653728323053575)
      ·
        refine ⟨26974798391480592484580363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983198927653728323053575 26974798391480592484580363)
        ·
          refine ⟨40462197587220888726870545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26974798391480592484580363 40462197587220888726870545)
          ·
            refine ⟨30346648190415666545152909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40462197587220888726870545 30346648190415666545152909)
            ·
              refine ⟨11379993071405874954432341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30346648190415666545152909 11379993071405874954432341)
              ·
                refine ⟨66679646902768798561127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11379993071405874954432341 66679646902768798561127)
                ·
                  rfl

theorem cell22_1753085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 9].length) (baseStart_1753085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753085 prefixEnd_1753085 := by exact prefixLift 1753085
  have htrace : WordTrace (prefixWord ++ tailWord_1753085) baseStart_1753085 baseEnd_1753085 := by
    simpa [prefixWord, tailWord_1753085, baseEnd_1753085] using wordTrace_append hprefix tailTrace_1753085
  have hstable : (prefixWord ++ tailWord_1753085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753085).length < 2 ^ (prefixWord ++ tailWord_1753085).sum := by decide
  have hdescent : baseEnd_1753085 < baseStart_1753085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753089 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1753089 : Nat := 118140960795 + 1753089 * 2 ^ 59
def prefixEnd_1753089 : Nat := 4983230072969 + 3 ^ 40 * 1753089 * 2
def baseEnd_1753089 : Nat := 600118191406664509950131

theorem tailTrace_1753089 : CollatzResearch.WordTrace tailWord_1753089 prefixEnd_1753089 600118191406664509950131 := by
  unfold tailWord_1753089
  simp only [CollatzResearch.WordTrace]
  refine ⟨63940408745865431609558321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42626939163910287739705547 63940408745865431609558321)
  ·
    refine ⟨47955306559399073707168741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63940408745865431609558321 47955306559399073707168741)
    ·
      refine ⟨8991619979887326320094139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47955306559399073707168741 8991619979887326320094139)
      ·
        refine ⟨13487429969830989480141209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991619979887326320094139 13487429969830989480141209)
        ·
          refine ⟨10115572477373242110105907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13487429969830989480141209 10115572477373242110105907)
          ·
            refine ⟨15173358716059863165158861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115572477373242110105907 15173358716059863165158861)
            ·
              refine ⟨5690009518522448686934573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15173358716059863165158861 5690009518522448686934573)
              ·
                refine ⟨2133753569445918257600465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5690009518522448686934573 2133753569445918257600465)
                ·
                  refine ⟨1600315177084438693200349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2133753569445918257600465 1600315177084438693200349)
                  ·
                    refine ⟨600118191406664509950131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1600315177084438693200349 600118191406664509950131)
                    ·
                      rfl

theorem cell22_1753089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1753089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753089 prefixEnd_1753089 := by exact prefixLift 1753089
  have htrace : WordTrace (prefixWord ++ tailWord_1753089) baseStart_1753089 baseEnd_1753089 := by
    simpa [prefixWord, tailWord_1753089, baseEnd_1753089] using wordTrace_append hprefix tailTrace_1753089
  have hstable : (prefixWord ++ tailWord_1753089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753089).length < 2 ^ (prefixWord ++ tailWord_1753089).sum := by decide
  have hdescent : baseEnd_1753089 < baseStart_1753089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753181 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 5]
def baseStart_1753181 : Nat := 118140960795 + 1753181 * 2 ^ 59
def prefixEnd_1753181 : Nat := 4983230072969 + 3 ^ 40 * 1753181 * 2
def baseEnd_1753181 : Nat := 200049894962268978883283

theorem tailTrace_1753181 : CollatzResearch.WordTrace tailWord_1753181 prefixEnd_1753181 200049894962268978883283 := by
  unfold tailWord_1753181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63943764261532131321907397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42629176174354754214604931 63943764261532131321907397)
  ·
    refine ⟨11989455799037274622857637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63943764261532131321907397 11989455799037274622857637)
    ·
      refine ⟨2248022962319488991785807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11989455799037274622857637 2248022962319488991785807)
      ·
        refine ⟨3372034443479233487678711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248022962319488991785807 3372034443479233487678711)
        ·
          refine ⟨5058051665218850231518067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372034443479233487678711 5058051665218850231518067)
          ·
            refine ⟨7587077497828275347277101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058051665218850231518067 7587077497828275347277101)
            ·
              refine ⟨2845154061685603255228913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7587077497828275347277101 2845154061685603255228913)
              ·
                refine ⟨2133865546264202441421685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845154061685603255228913 2133865546264202441421685)
                ·
                  refine ⟨200049894962268978883283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133865546264202441421685 200049894962268978883283)
                  ·
                    rfl

theorem cell22_1753181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_1753181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753181 prefixEnd_1753181 := by exact prefixLift 1753181
  have htrace : WordTrace (prefixWord ++ tailWord_1753181) baseStart_1753181 baseEnd_1753181 := by
    simpa [prefixWord, tailWord_1753181, baseEnd_1753181] using wordTrace_append hprefix tailTrace_1753181
  have hstable : (prefixWord ++ tailWord_1753181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753181).length < 2 ^ (prefixWord ++ tailWord_1753181).sum := by decide
  have hdescent : baseEnd_1753181 < baseStart_1753181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753226 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_1753226 : Nat := 118140960795 + 1753226 * 2 ^ 59
def prefixEnd_1753226 : Nat := 4983230072969 + 3 ^ 40 * 1753226 * 2
def baseEnd_1753226 : Nat := 200055029768813939758237

theorem tailTrace_1753226 : CollatzResearch.WordTrace tailWord_1753226 prefixEnd_1753226 200055029768813939758237 := by
  unfold tailWord_1753226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15986351386592276001823883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42630270364246069338197021 15986351386592276001823883)
  ·
    refine ⟨23979527079888414002735825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15986351386592276001823883 23979527079888414002735825)
    ·
      refine ⟨17984645309916310502051869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23979527079888414002735825 17984645309916310502051869)
      ·
        refine ⟨6744241991218616438269451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17984645309916310502051869 6744241991218616438269451)
        ·
          refine ⟨10116362986827924657404177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744241991218616438269451 10116362986827924657404177)
          ·
            refine ⟨7587272240120943493053133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10116362986827924657404177 7587272240120943493053133)
            ·
              refine ⟨2845227090045353809894925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7587272240120943493053133 2845227090045353809894925)
              ·
                refine ⟨1066960158767007678710597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2845227090045353809894925 1066960158767007678710597)
                ·
                  refine ⟨200055029768813939758237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066960158767007678710597 200055029768813939758237)
                  ·
                    rfl

theorem cell22_1753226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_1753226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753226 prefixEnd_1753226 := by exact prefixLift 1753226
  have htrace : WordTrace (prefixWord ++ tailWord_1753226) baseStart_1753226 baseEnd_1753226 := by
    simpa [prefixWord, tailWord_1753226, baseEnd_1753226] using wordTrace_append hprefix tailTrace_1753226
  have hstable : (prefixWord ++ tailWord_1753226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753226).length < 2 ^ (prefixWord ++ tailWord_1753226).sum := by decide
  have hdescent : baseEnd_1753226 < baseStart_1753226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753262 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1753262 : Nat := 118140960795 + 1753262 * 2 ^ 59
def prefixEnd_1753262 : Nat := 4983230072969 + 3 ^ 40 * 1753262 * 2
def baseEnd_1753262 : Nat := 600177412842149725374601

theorem tailTrace_1753262 : CollatzResearch.WordTrace tailWord_1753262 prefixEnd_1753262 600177412842149725374601 := by
  unfold tailWord_1753262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993339821779835269450755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42631145716159121437070693 7993339821779835269450755)
  ·
    refine ⟨11990009732669752904176133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993339821779835269450755 11990009732669752904176133)
    ·
      refine ⟨2248126824875578669533025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11990009732669752904176133 2248126824875578669533025)
      ·
        refine ⟨1686095118656684002149769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2248126824875578669533025 1686095118656684002149769)
        ·
          refine ⟨1264571338992513001612327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1686095118656684002149769 1264571338992513001612327)
          ·
            refine ⟨1896857008488769502418491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264571338992513001612327 1896857008488769502418491)
            ·
              refine ⟨2845285512733154253627737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896857008488769502418491 2845285512733154253627737)
              ·
                refine ⟨2133964134549865690220803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845285512733154253627737 2133964134549865690220803)
                ·
                  refine ⟨3200946201824798535331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133964134549865690220803 3200946201824798535331205)
                  ·
                    refine ⟨600177412842149725374601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200946201824798535331205 600177412842149725374601)
                    ·
                      rfl

theorem cell22_1753262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1753262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753262 prefixEnd_1753262 := by exact prefixLift 1753262
  have htrace : WordTrace (prefixWord ++ tailWord_1753262) baseStart_1753262 baseEnd_1753262 := by
    simpa [prefixWord, tailWord_1753262, baseEnd_1753262] using wordTrace_append hprefix tailTrace_1753262
  have hstable : (prefixWord ++ tailWord_1753262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753262).length < 2 ^ (prefixWord ++ tailWord_1753262).sum := by decide
  have hdescent : baseEnd_1753262 < baseStart_1753262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753329 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1753329 : Nat := 118140960795 + 1753329 * 2 ^ 59
def prefixEnd_1753329 : Nat := 4983230072969 + 3 ^ 40 * 1753329 * 2
def baseEnd_1753329 : Nat := 600200348311383883949395

theorem tailTrace_1753329 : CollatzResearch.WordTrace tailWord_1753329 prefixEnd_1753329 600200348311383883949395 := by
  unfold tailWord_1753329
  simp only [CollatzResearch.WordTrace]
  refine ⟨63949162264995952598295041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42632774843330635065530027 63949162264995952598295041)
  ·
    refine ⟨47961871698746964448721281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63949162264995952598295041 47961871698746964448721281)
    ·
      refine ⟨35971403774060223336540961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47961871698746964448721281 35971403774060223336540961)
      ·
        refine ⟨26978552830545167502405721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35971403774060223336540961 26978552830545167502405721)
        ·
          refine ⟨20233914622908875626804291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26978552830545167502405721 20233914622908875626804291)
          ·
            refine ⟨30350871934363313440206437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20233914622908875626804291 30350871934363313440206437)
            ·
              refine ⟨5690788487693121270038707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30350871934363313440206437 5690788487693121270038707)
              ·
                refine ⟨8536182731539681905058061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5690788487693121270038707 8536182731539681905058061)
                ·
                  refine ⟨3201068524327380714396773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8536182731539681905058061 3201068524327380714396773)
                  ·
                    refine ⟨600200348311383883949395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3201068524327380714396773 600200348311383883949395)
                    ·
                      rfl

theorem cell22_1753329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1753329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753329 prefixEnd_1753329 := by exact prefixLift 1753329
  have htrace : WordTrace (prefixWord ++ tailWord_1753329) baseStart_1753329 baseEnd_1753329 := by
    simpa [prefixWord, tailWord_1753329, baseEnd_1753329] using wordTrace_append hprefix tailTrace_1753329
  have hstable : (prefixWord ++ tailWord_1753329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753329).length < 2 ^ (prefixWord ++ tailWord_1753329).sum := by decide
  have hdescent : baseEnd_1753329 < baseStart_1753329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753361 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 4]
def baseStart_1753361 : Nat := 118140960795 + 1753361 * 2 ^ 59
def prefixEnd_1753361 : Nat := 4983230072969 + 3 ^ 40 * 1753361 * 2
def baseEnd_1753361 : Nat := 200070434188448822383099

theorem tailTrace_1753361 : CollatzResearch.WordTrace tailWord_1753361 prefixEnd_1753361 200070434188448822383099 := by
  unfold tailWord_1753361
  simp only [CollatzResearch.WordTrace]
  refine ⟨63950329400880022063459937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42633552933920014708973291 63950329400880022063459937)
  ·
    refine ⟨47962747050660016547594953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63950329400880022063459937 47962747050660016547594953)
    ·
      refine ⟨35972060287995012410696215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47962747050660016547594953 35972060287995012410696215)
      ·
        refine ⟨53958090431992518616044323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35972060287995012410696215 53958090431992518616044323)
        ·
          refine ⟨80937135647988777924066485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53958090431992518616044323 80937135647988777924066485)
          ·
            refine ⟨7587856466998947930381233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80937135647988777924066485 7587856466998947930381233)
            ·
              refine ⟨5690892350249210947785925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7587856466998947930381233 5690892350249210947785925)
              ·
                refine ⟨1067042315671727052709861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5690892350249210947785925 1067042315671727052709861)
                ·
                  refine ⟨200070434188448822383099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067042315671727052709861 200070434188448822383099)
                  ·
                    rfl

theorem cell22_1753361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 4].length) (baseStart_1753361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753361 prefixEnd_1753361 := by exact prefixLift 1753361
  have htrace : WordTrace (prefixWord ++ tailWord_1753361) baseStart_1753361 baseEnd_1753361 := by
    simpa [prefixWord, tailWord_1753361, baseEnd_1753361] using wordTrace_append hprefix tailTrace_1753361
  have hstable : (prefixWord ++ tailWord_1753361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753361).length < 2 ^ (prefixWord ++ tailWord_1753361).sum := by decide
  have hdescent : baseEnd_1753361 < baseStart_1753361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753376 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_1753376 : Nat := 118140960795 + 1753376 * 2 ^ 59
def prefixEnd_1753376 : Nat := 4983230072969 + 3 ^ 40 * 1753376 * 2
def baseEnd_1753376 : Nat := 600216437371891428024251

theorem tailTrace_1753376 : CollatzResearch.WordTrace tailWord_1753376 prefixEnd_1753376 600216437371891428024251 := by
  unfold tailWord_1753376
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975438247912839812627991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42633917663883786416837321 31975438247912839812627991)
  ·
    refine ⟨47963157371869259718941987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31975438247912839812627991 47963157371869259718941987)
    ·
      refine ⟨71944736057803889578412981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47963157371869259718941987 71944736057803889578412981)
      ·
        refine ⟨6744819005419114647976217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71944736057803889578412981 6744819005419114647976217)
        ·
          refine ⟨5058614254064335985982163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6744819005419114647976217 5058614254064335985982163)
          ·
            refine ⟨7587921381096503978973245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058614254064335985982163 7587921381096503978973245)
            ·
              refine ⟨2845470517911188992114967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7587921381096503978973245 2845470517911188992114967)
              ·
                refine ⟨4268205776866783488172451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845470517911188992114967 4268205776866783488172451)
                ·
                  refine ⟨6402308665300175232258677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268205776866783488172451 6402308665300175232258677)
                  ·
                    refine ⟨600216437371891428024251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6402308665300175232258677 600216437371891428024251)
                    ·
                      rfl

theorem cell22_1753376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_1753376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753376 prefixEnd_1753376 := by exact prefixLift 1753376
  have htrace : WordTrace (prefixWord ++ tailWord_1753376) baseStart_1753376 baseEnd_1753376 := by
    simpa [prefixWord, tailWord_1753376, baseEnd_1753376] using wordTrace_append hprefix tailTrace_1753376
  have hstable : (prefixWord ++ tailWord_1753376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753376).length < 2 ^ (prefixWord ++ tailWord_1753376).sum := by decide
  have hdescent : baseEnd_1753376 < baseStart_1753376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753406 : List Nat := [4, 2, 1, 2, 1, 4, 8]
def baseStart_1753406 : Nat := 118140960795 + 1753406 * 2 ^ 59
def prefixEnd_1753406 : Nat := 4983230072969 + 3 ^ 40 * 1753406 * 2
def baseEnd_1753406 : Nat := 22230618777221531473117

theorem tailTrace_1753406 : CollatzResearch.WordTrace tailWord_1753406 prefixEnd_1753406 22230618777221531473117 := by
  unfold tailWord_1753406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993996335714624343606009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42634647123811329832565381 7993996335714624343606009)
  ·
    refine ⟨5995497251785968257704507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7993996335714624343606009 5995497251785968257704507)
    ·
      refine ⟨8993245877678952386556761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5995497251785968257704507 8993245877678952386556761)
      ·
        refine ⟨6744934408259214289917571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8993245877678952386556761 6744934408259214289917571)
        ·
          refine ⟨10117401612388821434876357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744934408259214289917571 10117401612388821434876357)
          ·
            refine ⟨1897012802322904019039317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10117401612388821434876357 1897012802322904019039317)
            ·
              refine ⟨22230618777221531473117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1897012802322904019039317 22230618777221531473117)
              ·
                rfl

theorem cell22_1753406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 8].length) (baseStart_1753406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753406 prefixEnd_1753406 := by exact prefixLift 1753406
  have htrace : WordTrace (prefixWord ++ tailWord_1753406) baseStart_1753406 baseEnd_1753406 := by
    simpa [prefixWord, tailWord_1753406, baseEnd_1753406] using wordTrace_append hprefix tailTrace_1753406
  have hstable : (prefixWord ++ tailWord_1753406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753406).length < 2 ^ (prefixWord ++ tailWord_1753406).sum := by decide
  have hdescent : baseEnd_1753406 < baseStart_1753406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753412 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_1753412 : Nat := 118140960795 + 1753412 * 2 ^ 59
def prefixEnd_1753412 : Nat := 4983230072969 + 3 ^ 40 * 1753412 * 2
def baseEnd_1753412 : Nat := 200076253635866444708047

theorem tailTrace_1753412 : CollatzResearch.WordTrace tailWord_1753412 prefixEnd_1753412 200076253635866444708047 := by
  unfold tailWord_1753412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31976094761847628886783245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42634793015796838515710993 31976094761847628886783245)
  ·
    refine ⟨11991035535692860832543717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31976094761847628886783245 11991035535692860832543717)
    ·
      refine ⟨2248319162942411406101947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11991035535692860832543717 2248319162942411406101947)
      ·
        refine ⟨3372478744413617109152921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248319162942411406101947 3372478744413617109152921)
        ·
          refine ⟨2529359058310212831864691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3372478744413617109152921 2529359058310212831864691)
          ·
            refine ⟨3794038587465319247797037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529359058310212831864691 3794038587465319247797037)
            ·
              refine ⟨1422764470299494717923889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3794038587465319247797037 1422764470299494717923889)
              ·
                refine ⟨1067073352724621038442917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422764470299494717923889 1067073352724621038442917)
                ·
                  refine ⟨200076253635866444708047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067073352724621038442917 200076253635866444708047)
                  ·
                    rfl

theorem cell22_1753412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_1753412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753412 prefixEnd_1753412 := by exact prefixLift 1753412
  have htrace : WordTrace (prefixWord ++ tailWord_1753412) baseStart_1753412 baseEnd_1753412 := by
    simpa [prefixWord, tailWord_1753412, baseEnd_1753412] using wordTrace_append hprefix tailTrace_1753412
  have hstable : (prefixWord ++ tailWord_1753412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753412).length < 2 ^ (prefixWord ++ tailWord_1753412).sum := by decide
  have hdescent : baseEnd_1753412 < baseStart_1753412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753481 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 3, 4]
def baseStart_1753481 : Nat := 118140960795 + 1753481 * 2 ^ 59
def prefixEnd_1753481 : Nat := 4983230072969 + 3 ^ 40 * 1753481 * 2
def baseEnd_1753481 : Nat := 600252381017706154148929

theorem tailTrace_1753481 : CollatzResearch.WordTrace tailWord_1753481 prefixEnd_1753481 600252381017706154148929 := by
  unfold tailWord_1753481
  simp only [CollatzResearch.WordTrace]
  refine ⟨63954706160445282557828297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42636470773630188371885531 63954706160445282557828297)
  ·
    refine ⟨47966029620333961918371223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63954706160445282557828297 47966029620333961918371223)
    ·
      refine ⟨71949044430500942877556835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47966029620333961918371223 71949044430500942877556835)
      ·
        refine ⟨107923566645751414316335253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71949044430500942877556835 107923566645751414316335253)
        ·
          refine ⟨5058917186519597546078215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107923566645751414316335253 5058917186519597546078215)
          ·
            refine ⟨7588375779779396319117323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058917186519597546078215 7588375779779396319117323)
            ·
              refine ⟨11382563669669094478675985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588375779779396319117323 11382563669669094478675985)
              ·
                refine ⟨8536922752251820859006989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11382563669669094478675985 8536922752251820859006989)
                ·
                  refine ⟨3201346032094432822127621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8536922752251820859006989 3201346032094432822127621)
                  ·
                    refine ⟨600252381017706154148929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3201346032094432822127621 600252381017706154148929)
                    ·
                      rfl

theorem cell22_1753481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_1753481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753481 prefixEnd_1753481 := by exact prefixLift 1753481
  have htrace : WordTrace (prefixWord ++ tailWord_1753481) baseStart_1753481 baseEnd_1753481 := by
    simpa [prefixWord, tailWord_1753481, baseEnd_1753481] using wordTrace_append hprefix tailTrace_1753481
  have hstable : (prefixWord ++ tailWord_1753481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753481).length < 2 ^ (prefixWord ++ tailWord_1753481).sum := by decide
  have hdescent : baseEnd_1753481 < baseStart_1753481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753496 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_1753496 : Nat := 118140960795 + 1753496 * 2 ^ 59
def prefixEnd_1753496 : Nat := 4983230072969 + 3 ^ 40 * 1753496 * 2
def baseEnd_1753496 : Nat := 200085838608083705007961

theorem tailTrace_1753496 : CollatzResearch.WordTrace tailWord_1753496 prefixEnd_1753496 200085838608083705007961 := by
  unfold tailWord_1753496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31977626627695470059812171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42636835503593960079749561 31977626627695470059812171)
  ·
    refine ⟨47966439941543205089718257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31977626627695470059812171 47966439941543205089718257)
    ·
      refine ⟨35974829956157403817288693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47966439941543205089718257 35974829956157403817288693)
      ·
        refine ⟨3372640308389756607870815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35974829956157403817288693 3372640308389756607870815)
        ·
          refine ⟨5058960462584634911806223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372640308389756607870815 5058960462584634911806223)
          ·
            refine ⟨7588440693876952367709335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058960462584634911806223 7588440693876952367709335)
            ·
              refine ⟨11382661040815428551564003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588440693876952367709335 11382661040815428551564003)
              ·
                refine ⟨17073991561223142827346005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11382661040815428551564003 17073991561223142827346005)
                ·
                  refine ⟨200085838608083705007961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17073991561223142827346005 200085838608083705007961)
                  ·
                    rfl

theorem cell22_1753496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_1753496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753496 prefixEnd_1753496 := by exact prefixLift 1753496
  have htrace : WordTrace (prefixWord ++ tailWord_1753496) baseStart_1753496 baseEnd_1753496 := by
    simpa [prefixWord, tailWord_1753496, baseEnd_1753496] using wordTrace_append hprefix tailTrace_1753496
  have hstable : (prefixWord ++ tailWord_1753496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753496).length < 2 ^ (prefixWord ++ tailWord_1753496).sum := by decide
  have hdescent : baseEnd_1753496 < baseStart_1753496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753558 : List Nat := [5, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1753558 : Nat := 118140960795 + 1753558 * 2 ^ 59
def prefixEnd_1753558 : Nat := 4983230072969 + 3 ^ 40 * 1753558 * 2
def baseEnd_1753558 : Nat := 66697637743478179997077

theorem tailTrace_1753558 : CollatzResearch.WordTrace tailWord_1753558 prefixEnd_1753558 66697637743478179997077 := by
  unfold tailWord_1753558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997344661322895294273833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42638343054110883138920885 3997344661322895294273833)
  ·
    refine ⟨2998008495992171470705375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3997344661322895294273833 2998008495992171470705375)
    ·
      refine ⟨4497012743988257206058063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998008495992171470705375 4497012743988257206058063)
      ·
        refine ⟨6745519115982385809087095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497012743988257206058063 6745519115982385809087095)
        ·
          refine ⟨10118278673973578713630643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745519115982385809087095 10118278673973578713630643)
          ·
            refine ⟨15177418010960368070445965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118278673973578713630643 15177418010960368070445965)
            ·
              refine ⟨5691531754110138026417237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15177418010960368070445965 5691531754110138026417237)
              ·
                refine ⟨66697637743478179997077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5691531754110138026417237 66697637743478179997077)
                ·
                  rfl

theorem cell22_1753558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1753558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753558 prefixEnd_1753558 := by exact prefixLift 1753558
  have htrace : WordTrace (prefixWord ++ tailWord_1753558) baseStart_1753558 baseEnd_1753558 := by
    simpa [prefixWord, tailWord_1753558, baseEnd_1753558] using wordTrace_append hprefix tailTrace_1753558
  have hstable : (prefixWord ++ tailWord_1753558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753558).length < 2 ^ (prefixWord ++ tailWord_1753558).sum := by decide
  have hdescent : baseEnd_1753558 < baseStart_1753558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753652 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1753652 : Nat := 118140960795 + 1753652 * 2 ^ 59
def prefixEnd_1753652 : Nat := 4983230072969 + 3 ^ 40 * 1753652 * 2
def baseEnd_1753652 : Nat := 600310917812318708123405

theorem tailTrace_1753652 : CollatzResearch.WordTrace tailWord_1753652 prefixEnd_1753652 600310917812318708123405 := by
  unfold tailWord_1753652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31980471521412889381151605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42640628695217185841535473 31980471521412889381151605)
  ·
    refine ⟨2998169205132458379482963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31980471521412889381151605 2998169205132458379482963)
    ·
      refine ⟨4497253807698687569224445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998169205132458379482963 4497253807698687569224445)
      ·
        refine ⟨1686470177887007838459167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4497253807698687569224445 1686470177887007838459167)
        ·
          refine ⟨2529705266830511757688751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686470177887007838459167 2529705266830511757688751)
          ·
            refine ⟨3794557900245767636533127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529705266830511757688751 3794557900245767636533127)
            ·
              refine ⟨5691836850368651454799691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794557900245767636533127 5691836850368651454799691)
              ·
                refine ⟨8537755275552977182199537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691836850368651454799691 8537755275552977182199537)
                ·
                  refine ⟨6403316456664732886649653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8537755275552977182199537 6403316456664732886649653)
                  ·
                    refine ⟨600310917812318708123405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6403316456664732886649653 600310917812318708123405)
                    ·
                      rfl

theorem cell22_1753652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1753652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753652 prefixEnd_1753652 := by exact prefixLift 1753652
  have htrace : WordTrace (prefixWord ++ tailWord_1753652) baseStart_1753652 baseEnd_1753652 := by
    simpa [prefixWord, tailWord_1753652, baseEnd_1753652] using wordTrace_append hprefix tailTrace_1753652
  have hstable : (prefixWord ++ tailWord_1753652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753652).length < 2 ^ (prefixWord ++ tailWord_1753652).sum := by decide
  have hdescent : baseEnd_1753652 < baseStart_1753652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753663 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 1, 5]
def baseStart_1753663 : Nat := 118140960795 + 1753663 * 2 ^ 59
def prefixEnd_1753663 : Nat := 4983230072969 + 3 ^ 40 * 1753663 * 2
def baseEnd_1753663 : Nat := 600314683337118346098371

theorem tailTrace_1753663 : CollatzResearch.WordTrace tailWord_1753663 prefixEnd_1753663 600314683337118346098371 := by
  unfold tailWord_1753663
  simp only [CollatzResearch.WordTrace]
  refine ⟨63961344245785927640953643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42640896163857285093969095 63961344245785927640953643)
  ·
    refine ⟨95942016368678891461430465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63961344245785927640953643 95942016368678891461430465)
    ·
      refine ⟨71956512276509168596072849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95942016368678891461430465 71956512276509168596072849)
      ·
        refine ⟨53967384207381876447054637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71956512276509168596072849 53967384207381876447054637)
        ·
          refine ⟨20237769077768203667645489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53967384207381876447054637 20237769077768203667645489)
          ·
            refine ⟨15178326808326152750734117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20237769077768203667645489 15178326808326152750734117)
            ·
              refine ⟨2845936276561153640762647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15178326808326152750734117 2845936276561153640762647)
              ·
                refine ⟨4268904414841730461143971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845936276561153640762647 4268904414841730461143971)
                ·
                  refine ⟨6403356622262595691715957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268904414841730461143971 6403356622262595691715957)
                  ·
                    refine ⟨600314683337118346098371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6403356622262595691715957 600314683337118346098371)
                    ·
                      rfl

theorem cell22_1753663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_1753663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753663 prefixEnd_1753663 := by exact prefixLift 1753663
  have htrace : WordTrace (prefixWord ++ tailWord_1753663) baseStart_1753663 baseEnd_1753663 := by
    simpa [prefixWord, tailWord_1753663, baseEnd_1753663] using wordTrace_append hprefix tailTrace_1753663
  have hstable : (prefixWord ++ tailWord_1753663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753663).length < 2 ^ (prefixWord ++ tailWord_1753663).sum := by decide
  have hdescent : baseEnd_1753663 < baseStart_1753663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753697 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1753697 : Nat := 118140960795 + 1753697 * 2 ^ 59
def prefixEnd_1753697 : Nat := 4983230072969 + 3 ^ 40 * 1753697 * 2
def baseEnd_1753697 : Nat := 600326322231953590748267

theorem tailTrace_1753697 : CollatzResearch.WordTrace tailWord_1753697 prefixEnd_1753697 600326322231953590748267 := by
  unfold tailWord_1753697
  simp only [CollatzResearch.WordTrace]
  refine ⟨63962584327662751447691345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42641722885108500965127563 63962584327662751447691345)
  ·
    refine ⟨47971938245747063585768509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63962584327662751447691345 47971938245747063585768509)
    ·
      refine ⟨17989476842155148844663191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47971938245747063585768509 17989476842155148844663191)
      ·
        refine ⟨26984215263232723266994787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17989476842155148844663191 26984215263232723266994787)
        ·
          refine ⟨40476322894849084900492181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26984215263232723266994787 40476322894849084900492181)
          ·
            refine ⟨1897327635696050854710571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40476322894849084900492181 1897327635696050854710571)
            ·
              refine ⟨2845991453544076282065857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897327635696050854710571 2845991453544076282065857)
              ·
                refine ⟨2134493590158057211549393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2845991453544076282065857 2134493590158057211549393)
                ·
                  refine ⟨1600870192618542908662045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2134493590158057211549393 1600870192618542908662045)
                  ·
                    refine ⟨600326322231953590748267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1600870192618542908662045 600326322231953590748267)
                    ·
                      rfl

theorem cell22_1753697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1753697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753697 prefixEnd_1753697 := by exact prefixLift 1753697
  have htrace : WordTrace (prefixWord ++ tailWord_1753697) baseStart_1753697 baseEnd_1753697 := by
    simpa [prefixWord, tailWord_1753697, baseEnd_1753697] using wordTrace_append hprefix tailTrace_1753697
  have hstable : (prefixWord ++ tailWord_1753697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753697).length < 2 ^ (prefixWord ++ tailWord_1753697).sum := by decide
  have hdescent : baseEnd_1753697 < baseStart_1753697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753714 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_1753714 : Nat := 118140960795 + 1753714 * 2 ^ 59
def prefixEnd_1753714 : Nat := 4983230072969 + 3 ^ 40 * 1753714 * 2
def baseEnd_1753714 : Nat := 600332141679371213073215

theorem tailTrace_1753714 : CollatzResearch.WordTrace tailWord_1753714 prefixEnd_1753714 600332141679371213073215 := by
  unfold tailWord_1753714
  simp only [CollatzResearch.WordTrace]
  refine ⟨15990801092150290837765049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42642136245734108900706797 15990801092150290837765049)
  ·
    refine ⟨11993100819112718128323787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15990801092150290837765049 11993100819112718128323787)
    ·
      refine ⟨17989651228669077192485681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11993100819112718128323787 17989651228669077192485681)
      ·
        refine ⟨13492238421501807894364261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17989651228669077192485681 13492238421501807894364261)
        ·
          refine ⟨2529794704031588980193299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13492238421501807894364261 2529794704031588980193299)
          ·
            refine ⟨3794692056047383470289949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529794704031588980193299 3794692056047383470289949)
            ·
              refine ⟨1423009521017768801358731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3794692056047383470289949 1423009521017768801358731)
              ·
                refine ⟨2134514281526653202038097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423009521017768801358731 2134514281526653202038097)
                ·
                  refine ⟨1600885711144989901528573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2134514281526653202038097 1600885711144989901528573)
                  ·
                    refine ⟨600332141679371213073215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1600885711144989901528573 600332141679371213073215)
                    ·
                      rfl

theorem cell22_1753714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_1753714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753714 prefixEnd_1753714 := by exact prefixLift 1753714
  have htrace : WordTrace (prefixWord ++ tailWord_1753714) baseStart_1753714 baseEnd_1753714 := by
    simpa [prefixWord, tailWord_1753714, baseEnd_1753714] using wordTrace_append hprefix tailTrace_1753714
  have hstable : (prefixWord ++ tailWord_1753714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753714).length < 2 ^ (prefixWord ++ tailWord_1753714).sum := by decide
  have hdescent : baseEnd_1753714 < baseStart_1753714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753832 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1753832 : Nat := 118140960795 + 1753832 * 2 ^ 59
def prefixEnd_1753832 : Nat := 4983230072969 + 3 ^ 40 * 1753832 * 2
def baseEnd_1753832 : Nat := 600372535490858238622853

theorem tailTrace_1753832 : CollatzResearch.WordTrace tailWord_1753832 prefixEnd_1753832 600372535490858238622853 := by
  unfold tailWord_1753832
  simp only [CollatzResearch.WordTrace]
  refine ⟨31983754091086834751927875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42645005454782446335903833 31983754091086834751927875)
  ·
    refine ⟨47975631136630252127891813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31983754091086834751927875 47975631136630252127891813)
    ·
      refine ⟨8995430838118172273979715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47975631136630252127891813 8995430838118172273979715)
      ·
        refine ⟨13493146257177258410969573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995430838118172273979715 13493146257177258410969573)
        ·
          refine ⟨2529964923220735952056795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13493146257177258410969573 2529964923220735952056795)
          ·
            refine ⟨3794947384831103928085193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529964923220735952056795 3794947384831103928085193)
            ·
              refine ⟨2846210538623327946063895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794947384831103928085193 2846210538623327946063895)
              ·
                refine ⟨4269315807934991919095843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846210538623327946063895 4269315807934991919095843)
                ·
                  refine ⟨6403973711902487878643765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269315807934991919095843 6403973711902487878643765)
                  ·
                    refine ⟨600372535490858238622853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6403973711902487878643765 600372535490858238622853)
                    ·
                      rfl

theorem cell22_1753832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1753832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753832 prefixEnd_1753832 := by exact prefixLift 1753832
  have htrace : WordTrace (prefixWord ++ tailWord_1753832) baseStart_1753832 baseEnd_1753832 := by
    simpa [prefixWord, tailWord_1753832, baseEnd_1753832] using wordTrace_append hprefix tailTrace_1753832
  have hstable : (prefixWord ++ tailWord_1753832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753832).length < 2 ^ (prefixWord ++ tailWord_1753832).sum := by decide
  have hdescent : baseEnd_1753832 < baseStart_1753832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753877 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1753877 : Nat := 118140960795 + 1753877 * 2 ^ 59
def prefixEnd_1753877 : Nat := 4983230072969 + 3 ^ 40 * 1753877 * 2
def baseEnd_1753877 : Nat := 600387939910493121247715

theorem tailTrace_1753877 : CollatzResearch.WordTrace tailWord_1753877 prefixEnd_1753877 600387939910493121247715 := by
  unfold tailWord_1753877
  simp only [CollatzResearch.WordTrace]
  refine ⟨63969149467010642189243885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42646099644673761459495923 63969149467010642189243885)
  ·
    refine ⟨23988431050128990820966457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63969149467010642189243885 23988431050128990820966457)
    ·
      refine ⟨17991323287596743115724843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23988431050128990820966457 17991323287596743115724843)
      ·
        refine ⟨26986984931395114673587265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991323287596743115724843 26986984931395114673587265)
        ·
          refine ⟨20240238698546336005190449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26986984931395114673587265 20240238698546336005190449)
          ·
            refine ⟨15180179023909752003892837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20240238698546336005190449 15180179023909752003892837)
            ·
              refine ⟨2846283566983078500729907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15180179023909752003892837 2846283566983078500729907)
              ·
                refine ⟨4269425350474617751094861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846283566983078500729907 4269425350474617751094861)
                ·
                  refine ⟨1601034506427981656660573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4269425350474617751094861 1601034506427981656660573)
                  ·
                    refine ⟨600387939910493121247715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601034506427981656660573 600387939910493121247715)
                    ·
                      rfl

theorem cell22_1753877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1753877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753877 prefixEnd_1753877 := by exact prefixLift 1753877
  have htrace : WordTrace (prefixWord ++ tailWord_1753877) baseStart_1753877 baseEnd_1753877 := by
    simpa [prefixWord, tailWord_1753877, baseEnd_1753877] using wordTrace_append hprefix tailTrace_1753877
  have hstable : (prefixWord ++ tailWord_1753877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753877).length < 2 ^ (prefixWord ++ tailWord_1753877).sum := by decide
  have hdescent : baseEnd_1753877 < baseStart_1753877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753954 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1753954 : Nat := 118140960795 + 1753954 * 2 ^ 59
def prefixEnd_1753954 : Nat := 4983230072969 + 3 ^ 40 * 1753954 * 2
def baseEnd_1753954 : Nat := 600414298584090587072479

theorem tailTrace_1753954 : CollatzResearch.WordTrace tailWord_1753954 prefixEnd_1753954 600414298584090587072479 := by
  unfold tailWord_1753954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992989471932921084949229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42647971925154456226531277 15992989471932921084949229)
  ·
    refine ⟨5997371051974845406855961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15992989471932921084949229 5997371051974845406855961)
    ·
      refine ⟨4498028288981134055141971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5997371051974845406855961 4498028288981134055141971)
      ·
        refine ⟨6747042433471701082712957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498028288981134055141971 6747042433471701082712957)
        ·
          refine ⟨2530140912551887906017359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6747042433471701082712957 2530140912551887906017359)
          ·
            refine ⟨3795211368827831859026039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530140912551887906017359 3795211368827831859026039)
            ·
              refine ⟨5692817053241747788539059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795211368827831859026039 5692817053241747788539059)
              ·
                refine ⟨8539225579862621682808589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5692817053241747788539059 8539225579862621682808589)
                ·
                  refine ⟨3202209592448483131053221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8539225579862621682808589 3202209592448483131053221)
                  ·
                    refine ⟨600414298584090587072479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3202209592448483131053221 600414298584090587072479)
                    ·
                      rfl

theorem cell22_1753954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1753954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1753954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1753954 prefixEnd_1753954 := by exact prefixLift 1753954
  have htrace : WordTrace (prefixWord ++ tailWord_1753954) baseStart_1753954 baseEnd_1753954 := by
    simpa [prefixWord, tailWord_1753954, baseEnd_1753954] using wordTrace_append hprefix tailTrace_1753954
  have hstable : (prefixWord ++ tailWord_1753954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753954).length < 2 ^ (prefixWord ++ tailWord_1753954).sum := by decide
  have hdescent : baseEnd_1753954 < baseStart_1753954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754025 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 7]
def baseStart_1754025 : Nat := 118140960795 + 1754025 * 2 ^ 59
def prefixEnd_1754025 : Nat := 4983230072969 + 3 ^ 40 * 1754025 * 2
def baseEnd_1754025 : Nat := 200146201111690022849087

theorem tailTrace_1754025 : CollatzResearch.WordTrace tailWord_1754025 prefixEnd_1754025 200146201111690022849087 := by
  unfold tailWord_1754025
  simp only [CollatzResearch.WordTrace]
  refine ⟨63974547470474463465631529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42649698313649642310421019 63974547470474463465631529)
  ·
    refine ⟨47980910602855847599223647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63974547470474463465631529 47980910602855847599223647)
    ·
      refine ⟨71971365904283771398835471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47980910602855847599223647 71971365904283771398835471)
      ·
        refine ⟨107957048856425657098253207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71971365904283771398835471 107957048856425657098253207)
        ·
          refine ⟨161935573284638485647379811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107957048856425657098253207 161935573284638485647379811)
          ·
            refine ⟨242903359926957728471069717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161935573284638485647379811 242903359926957728471069717)
            ·
              refine ⟨11386094996576143522081393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242903359926957728471069717 11386094996576143522081393)
              ·
                refine ⟨8539571247432107641561045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11386094996576143522081393 8539571247432107641561045)
                ·
                  refine ⟨200146201111690022849087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8539571247432107641561045 200146201111690022849087)
                  ·
                    rfl

theorem cell22_1754025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_1754025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754025 prefixEnd_1754025 := by exact prefixLift 1754025
  have htrace : WordTrace (prefixWord ++ tailWord_1754025) baseStart_1754025 baseEnd_1754025 := by
    simpa [prefixWord, tailWord_1754025, baseEnd_1754025] using wordTrace_append hprefix tailTrace_1754025
  have hstable : (prefixWord ++ tailWord_1754025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754025).length < 2 ^ (prefixWord ++ tailWord_1754025).sum := by decide
  have hdescent : baseEnd_1754025 < baseStart_1754025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754046 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1754046 : Nat := 118140960795 + 1754046 * 2 ^ 59
def prefixEnd_1754046 : Nat := 4983230072969 + 3 ^ 40 * 1754046 * 2
def baseEnd_1754046 : Nat := 600445792064233013772197

theorem tailTrace_1754046 : CollatzResearch.WordTrace tailWord_1754046 prefixEnd_1754046 600445792064233013772197 := by
  unfold tailWord_1754046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996914175424798006518249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42650208935598922701430661 7996914175424798006518249)
  ·
    refine ⟨5997685631568598504888687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7996914175424798006518249 5997685631568598504888687)
    ·
      refine ⟨8996528447352897757333031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5997685631568598504888687 8996528447352897757333031)
      ·
        refine ⟨13494792671029346635999547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996528447352897757333031 13494792671029346635999547)
        ·
          refine ⟨20242189006544019953999321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13494792671029346635999547 20242189006544019953999321)
          ·
            refine ⟨15181641754908014965499491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20242189006544019953999321 15181641754908014965499491)
            ·
              refine ⟨22772462632362022448249237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15181641754908014965499491 22772462632362022448249237)
              ·
                refine ⟨1067459185891969802261683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22772462632362022448249237 1067459185891969802261683)
                ·
                  refine ⟨1601188778837954703392525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067459185891969802261683 1601188778837954703392525)
                  ·
                    refine ⟨600445792064233013772197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601188778837954703392525 600445792064233013772197)
                    ·
                      rfl

theorem cell22_1754046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1754046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754046 prefixEnd_1754046 := by exact prefixLift 1754046
  have htrace : WordTrace (prefixWord ++ tailWord_1754046) baseStart_1754046 baseEnd_1754046 := by
    simpa [prefixWord, tailWord_1754046, baseEnd_1754046] using wordTrace_append hprefix tailTrace_1754046
  have hstable : (prefixWord ++ tailWord_1754046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754046).length < 2 ^ (prefixWord ++ tailWord_1754046).sum := by decide
  have hdescent : baseEnd_1754046 < baseStart_1754046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754059 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 5]
def baseStart_1754059 : Nat := 118140960795 + 1754059 * 2 ^ 59
def prefixEnd_1754059 : Nat := 4983230072969 + 3 ^ 40 * 1754059 * 2
def baseEnd_1754059 : Nat := 200150080743301771065719

theorem tailTrace_1754059 : CollatzResearch.WordTrace tailWord_1754059 prefixEnd_1754059 200150080743301771065719 := by
  unfold tailWord_1754059
  simp only [CollatzResearch.WordTrace]
  refine ⟨63975787552351287272369231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42650525034900858181579487 63975787552351287272369231)
  ·
    refine ⟨95963681328526930908553847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63975787552351287272369231 95963681328526930908553847)
    ·
      refine ⟨143945521992790396362830771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95963681328526930908553847 143945521992790396362830771)
      ·
        refine ⟨215918282989185594544246157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143945521992790396362830771 215918282989185594544246157)
        ·
          refine ⟨80969356120944597954092309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215918282989185594544246157 80969356120944597954092309)
          ·
            refine ⟨3795438568169278029098077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80969356120944597954092309 3795438568169278029098077)
            ·
              refine ⟨1423289463063479260911779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3795438568169278029098077 1423289463063479260911779)
              ·
                refine ⟨2134934194595218891367669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423289463063479260911779 2134934194595218891367669)
                ·
                  refine ⟨200150080743301771065719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134934194595218891367669 200150080743301771065719)
                  ·
                    rfl

theorem cell22_1754059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 5].length) (baseStart_1754059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754059 prefixEnd_1754059 := by exact prefixLift 1754059
  have htrace : WordTrace (prefixWord ++ tailWord_1754059) baseStart_1754059 baseEnd_1754059 := by
    simpa [prefixWord, tailWord_1754059, baseEnd_1754059] using wordTrace_append hprefix tailTrace_1754059
  have hstable : (prefixWord ++ tailWord_1754059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754059).length < 2 ^ (prefixWord ++ tailWord_1754059).sum := by decide
  have hdescent : baseEnd_1754059 < baseStart_1754059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754110 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1754110 : Nat := 118140960795 + 1754110 * 2 ^ 59
def prefixEnd_1754110 : Nat := 4983230072969 + 3 ^ 40 * 1754110 * 2
def baseEnd_1754110 : Nat := 200155900190719393390667

theorem tailTrace_1754110 : CollatzResearch.WordTrace tailWord_1754110 prefixEnd_1754110 200155900190719393390667 := by
  unfold tailWord_1754110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997205959395815372809473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42651765116777681988317189 7997205959395815372809473)
  ·
    refine ⟨5997904469546861529607105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7997205959395815372809473 5997904469546861529607105)
    ·
      refine ⟨4498428352160146147205329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5997904469546861529607105 4498428352160146147205329)
      ·
        refine ⟨3373821264120109610403997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4498428352160146147205329 3373821264120109610403997)
        ·
          refine ⟨1265182974045041103901499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3373821264120109610403997 1265182974045041103901499)
          ·
            refine ⟨1897774461067561655852249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265182974045041103901499 1897774461067561655852249)
            ·
              refine ⟨1423330845800671241889187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1897774461067561655852249 1423330845800671241889187)
              ·
                refine ⟨2134996268701006862833781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423330845800671241889187 2134996268701006862833781)
                ·
                  refine ⟨200155900190719393390667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134996268701006862833781 200155900190719393390667)
                  ·
                    rfl

theorem cell22_1754110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1754110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754110 prefixEnd_1754110 := by exact prefixLift 1754110
  have htrace : WordTrace (prefixWord ++ tailWord_1754110) baseStart_1754110 baseEnd_1754110 := by
    simpa [prefixWord, tailWord_1754110, baseEnd_1754110] using wordTrace_append hprefix tailTrace_1754110
  have hstable : (prefixWord ++ tailWord_1754110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754110).length < 2 ^ (prefixWord ++ tailWord_1754110).sum := by decide
  have hdescent : baseEnd_1754110 < baseStart_1754110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754117 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1754117 : Nat := 118140960795 + 1754117 * 2 ^ 59
def prefixEnd_1754117 : Nat := 4983230072969 + 3 ^ 40 * 1754117 * 2
def baseEnd_1754117 : Nat := 600470096815212495246979

theorem tailTrace_1754117 : CollatzResearch.WordTrace tailWord_1754117 prefixEnd_1754117 600470096815212495246979 := by
  unfold tailWord_1754117
  simp only [CollatzResearch.WordTrace]
  refine ⟨63977902986141163177980605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42651935324094108785320403 63977902986141163177980605)
  ·
    refine ⟨23991713619802936191742727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63977902986141163177980605 23991713619802936191742727)
    ·
      refine ⟨35987570429704404287614091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23991713619802936191742727 35987570429704404287614091)
      ·
        refine ⟨53981355644556606431421137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35987570429704404287614091 53981355644556606431421137)
        ·
          refine ⟨40486016733417454823565853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53981355644556606431421137 40486016733417454823565853)
          ·
            refine ⟨15182256275031545558837195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40486016733417454823565853 15182256275031545558837195)
            ·
              refine ⟨22773384412547318338255793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15182256275031545558837195 22773384412547318338255793)
              ·
                refine ⟨17080038309410488753691845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22773384412547318338255793 17080038309410488753691845)
                ·
                  refine ⟨3202507183014466641317221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17080038309410488753691845 3202507183014466641317221)
                  ·
                    refine ⟨600470096815212495246979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3202507183014466641317221 600470096815212495246979)
                    ·
                      rfl

theorem cell22_1754117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1754117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754117 prefixEnd_1754117 := by exact prefixLift 1754117
  have htrace : WordTrace (prefixWord ++ tailWord_1754117) baseStart_1754117 baseEnd_1754117 := by
    simpa [prefixWord, tailWord_1754117, baseEnd_1754117] using wordTrace_append hprefix tailTrace_1754117
  have hstable : (prefixWord ++ tailWord_1754117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754117).length < 2 ^ (prefixWord ++ tailWord_1754117).sum := by decide
  have hdescent : baseEnd_1754117 < baseStart_1754117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754151 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1754151 : Nat := 118140960795 + 1754151 * 2 ^ 59
def prefixEnd_1754151 : Nat := 4983230072969 + 3 ^ 40 * 1754151 * 2
def baseEnd_1754151 : Nat := 600481735710047739896875

theorem tailTrace_1754151 : CollatzResearch.WordTrace tailWord_1754151 prefixEnd_1754151 600481735710047739896875 := by
  unfold tailWord_1754151
  simp only [CollatzResearch.WordTrace]
  refine ⟨63979143068017986984718307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42652762045345324656478871 63979143068017986984718307)
  ·
    refine ⟨95968714602026980477077461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63979143068017986984718307 95968714602026980477077461)
    ·
      refine ⟨2249266748485007354931503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 95968714602026980477077461 2249266748485007354931503)
      ·
        refine ⟨3373900122727511032397255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249266748485007354931503 3373900122727511032397255)
        ·
          refine ⟨5060850184091266548595883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373900122727511032397255 5060850184091266548595883)
          ·
            refine ⟨7591275276136899822893825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060850184091266548595883 7591275276136899822893825)
            ·
              refine ⟨5693456457102674867170369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7591275276136899822893825 5693456457102674867170369)
              ·
                refine ⟨4270092342827006150377777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693456457102674867170369 4270092342827006150377777)
                ·
                  refine ⟨3202569257120254612783333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4270092342827006150377777 3202569257120254612783333)
                  ·
                    refine ⟨600481735710047739896875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3202569257120254612783333 600481735710047739896875)
                    ·
                      rfl

theorem cell22_1754151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1754151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754151 prefixEnd_1754151 := by exact prefixLift 1754151
  have htrace : WordTrace (prefixWord ++ tailWord_1754151) baseStart_1754151 baseEnd_1754151 := by
    simpa [prefixWord, tailWord_1754151, baseEnd_1754151] using wordTrace_append hprefix tailTrace_1754151
  have hstable : (prefixWord ++ tailWord_1754151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754151).length < 2 ^ (prefixWord ++ tailWord_1754151).sum := by decide
  have hdescent : baseEnd_1754151 < baseStart_1754151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754162 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1754162 : Nat := 118140960795 + 1754162 * 2 ^ 59
def prefixEnd_1754162 : Nat := 4983230072969 + 3 ^ 40 * 1754162 * 2
def baseEnd_1754162 : Nat := 600485501234847377871841

theorem tailTrace_1754162 : CollatzResearch.WordTrace tailWord_1754162 prefixEnd_1754162 600485501234847377871841 := by
  unfold tailWord_1754162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994886067744533965842185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42653029513985423908912493 15994886067744533965842185)
  ·
    refine ⟨11996164550808400474381639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15994886067744533965842185 11996164550808400474381639)
    ·
      refine ⟨17994246826212600711572459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11996164550808400474381639 17994246826212600711572459)
      ·
        refine ⟨26991370239318901067358689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17994246826212600711572459 26991370239318901067358689)
        ·
          refine ⟨20243527679489175800519017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26991370239318901067358689 20243527679489175800519017)
          ·
            refine ⟨15182645759616881850389263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20243527679489175800519017 15182645759616881850389263)
            ·
              refine ⟨22773968639425322775583895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15182645759616881850389263 22773968639425322775583895)
              ·
                refine ⟨34160952959137984163375843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22773968639425322775583895 34160952959137984163375843)
                ·
                  refine ⟨51241429438706976245063765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34160952959137984163375843 51241429438706976245063765)
                  ·
                    refine ⟨600485501234847377871841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51241429438706976245063765 600485501234847377871841)
                    ·
                      rfl

theorem cell22_1754162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1754162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754162 prefixEnd_1754162 := by exact prefixLift 1754162
  have htrace : WordTrace (prefixWord ++ tailWord_1754162) baseStart_1754162 baseEnd_1754162 := by
    simpa [prefixWord, tailWord_1754162, baseEnd_1754162] using wordTrace_append hprefix tailTrace_1754162
  have hstable : (prefixWord ++ tailWord_1754162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754162).length < 2 ^ (prefixWord ++ tailWord_1754162).sum := by decide
  have hdescent : baseEnd_1754162 < baseStart_1754162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754166 : List Nat := [5, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1754166 : Nat := 118140960795 + 1754166 * 2 ^ 59
def prefixEnd_1754166 : Nat := 4983230072969 + 3 ^ 40 * 1754166 * 2
def baseEnd_1754166 : Nat := 66720763390732522307981

theorem tailTrace_1754166 : CollatzResearch.WordTrace tailWord_1754166 prefixEnd_1754166 66720763390732522307981 := by
  unfold tailWord_1754166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998730635185227784157147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42653126775309096364342901 3998730635185227784157147)
  ·
    refine ⟨5998095952777841676235721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998730635185227784157147 5998095952777841676235721)
    ·
      refine ⟨4498571964583381257176791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5998095952777841676235721 4498571964583381257176791)
      ·
        refine ⟨6747857946875071885765187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498571964583381257176791 6747857946875071885765187)
        ·
          refine ⟨10121786920312607828647781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747857946875071885765187 10121786920312607828647781)
          ·
            refine ⟨1897835047558613967871459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10121786920312607828647781 1897835047558613967871459)
            ·
              refine ⟨2846752571337920951807189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897835047558613967871459 2846752571337920951807189)
              ·
                refine ⟨66720763390732522307981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2846752571337920951807189 66720763390732522307981)
                ·
                  rfl

theorem cell22_1754166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1754166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754166 prefixEnd_1754166 := by exact prefixLift 1754166
  have htrace : WordTrace (prefixWord ++ tailWord_1754166) baseStart_1754166 baseEnd_1754166 := by
    simpa [prefixWord, tailWord_1754166, baseEnd_1754166] using wordTrace_append hprefix tailTrace_1754166
  have hstable : (prefixWord ++ tailWord_1754166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754166).length < 2 ^ (prefixWord ++ tailWord_1754166).sum := by decide
  have hdescent : baseEnd_1754166 < baseStart_1754166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754241 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1754241 : Nat := 118140960795 + 1754241 * 2 ^ 59
def prefixEnd_1754241 : Nat := 4983230072969 + 3 ^ 40 * 1754241 * 2
def baseEnd_1754241 : Nat := 600512544549317505146599

theorem tailTrace_1754241 : CollatzResearch.WordTrace tailWord_1754241 prefixEnd_1754241 600512544549317505146599 := by
  unfold tailWord_1754241
  simp only [CollatzResearch.WordTrace]
  refine ⟨63982425637691932355494577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42654950425127954903663051 63982425637691932355494577)
  ·
    refine ⟨47986819228268949266620933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63982425637691932355494577 47986819228268949266620933)
    ·
      refine ⟨8997528605300427987491425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47986819228268949266620933 8997528605300427987491425)
      ·
        refine ⟨6748146453975320990618569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997528605300427987491425 6748146453975320990618569)
        ·
          refine ⟨5061109840481490742963927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6748146453975320990618569 5061109840481490742963927)
          ·
            refine ⟨7591664760722236114445891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061109840481490742963927 7591664760722236114445891)
            ·
              refine ⟨11387497141083354171668837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7591664760722236114445891 11387497141083354171668837)
              ·
                refine ⟨2135155713953128907187907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11387497141083354171668837 2135155713953128907187907)
                ·
                  refine ⟨3202733570929693360781861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135155713953128907187907 3202733570929693360781861)
                  ·
                    refine ⟨600512544549317505146599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3202733570929693360781861 600512544549317505146599)
                    ·
                      rfl

theorem cell22_1754241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1754241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754241 prefixEnd_1754241 := by exact prefixLift 1754241
  have htrace : WordTrace (prefixWord ++ tailWord_1754241) baseStart_1754241 baseEnd_1754241 := by
    simpa [prefixWord, tailWord_1754241, baseEnd_1754241] using wordTrace_append hprefix tailTrace_1754241
  have hstable : (prefixWord ++ tailWord_1754241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754241).length < 2 ^ (prefixWord ++ tailWord_1754241).sum := by decide
  have hdescent : baseEnd_1754241 < baseStart_1754241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754273 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 4]
def baseStart_1754273 : Nat := 118140960795 + 1754273 * 2 ^ 59
def prefixEnd_1754273 : Nat := 4983230072969 + 3 ^ 40 * 1754273 * 2
def baseEnd_1754273 : Nat := 200174499601093362782167

theorem tailTrace_1754273 : CollatzResearch.WordTrace tailWord_1754273 prefixEnd_1754273 200174499601093362782167 := by
  unfold tailWord_1754273
  simp only [CollatzResearch.WordTrace]
  refine ⟨63983592773576001820659473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42655728515717334547106315 63983592773576001820659473)
  ·
    refine ⟨47987694580182001365494605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63983592773576001820659473 47987694580182001365494605)
    ·
      refine ⟨17995385467568250512060477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47987694580182001365494605 17995385467568250512060477)
      ·
        refine ⟨6748269550338093942022679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17995385467568250512060477 6748269550338093942022679)
        ·
          refine ⟨10122404325507140913034019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748269550338093942022679 10122404325507140913034019)
          ·
            refine ⟨15183606488260711369551029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122404325507140913034019 15183606488260711369551029)
            ·
              refine ⟨1423463108274441690895409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15183606488260711369551029 1423463108274441690895409)
              ·
                refine ⟨1067597331205831268171557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423463108274441690895409 1067597331205831268171557)
                ·
                  refine ⟨200174499601093362782167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067597331205831268171557 200174499601093362782167)
                  ·
                    rfl

theorem cell22_1754273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 4].length) (baseStart_1754273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754273 prefixEnd_1754273 := by exact prefixLift 1754273
  have htrace : WordTrace (prefixWord ++ tailWord_1754273) baseStart_1754273 baseEnd_1754273 := by
    simpa [prefixWord, tailWord_1754273, baseEnd_1754273] using wordTrace_append hprefix tailTrace_1754273
  have hstable : (prefixWord ++ tailWord_1754273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754273).length < 2 ^ (prefixWord ++ tailWord_1754273).sum := by decide
  have hdescent : baseEnd_1754273 < baseStart_1754273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754324 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1754324 : Nat := 118140960795 + 1754324 * 2 ^ 59
def prefixEnd_1754324 : Nat := 4983230072969 + 3 ^ 40 * 1754324 * 2
def baseEnd_1754324 : Nat := 200180319048510985107115

theorem tailTrace_1754324 : CollatzResearch.WordTrace tailWord_1754324 prefixEnd_1754324 200180319048510985107115 := by
  unfold tailWord_1754324
  simp only [CollatzResearch.WordTrace]
  refine ⟨31992726448195618765383013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42656968597594158353844017 31992726448195618765383013)
  ·
    refine ⟨5998636209036678518509315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31992726448195618765383013 5998636209036678518509315)
    ·
      refine ⟨8997954313555017777763973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998636209036678518509315 8997954313555017777763973)
      ·
        refine ⟨1687116433791565833330745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8997954313555017777763973 1687116433791565833330745)
        ·
          refine ⟨1265337325343674374998059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1687116433791565833330745 1265337325343674374998059)
          ·
            refine ⟨1898005988015511562497089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265337325343674374998059 1898005988015511562497089)
            ·
              refine ⟨1423504491011633671872817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898005988015511562497089 1423504491011633671872817)
              ·
                refine ⟨1067628368258725253904613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423504491011633671872817 1067628368258725253904613)
                ·
                  refine ⟨200180319048510985107115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067628368258725253904613 200180319048510985107115)
                  ·
                    rfl

theorem cell22_1754324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1754324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754324 prefixEnd_1754324 := by exact prefixLift 1754324
  have htrace : WordTrace (prefixWord ++ tailWord_1754324) baseStart_1754324 baseEnd_1754324 := by
    simpa [prefixWord, tailWord_1754324, baseEnd_1754324] using wordTrace_append hprefix tailTrace_1754324
  have hstable : (prefixWord ++ tailWord_1754324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754324).length < 2 ^ (prefixWord ++ tailWord_1754324).sum := by decide
  have hdescent : baseEnd_1754324 < baseStart_1754324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754346 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_1754346 : Nat := 118140960795 + 1754346 * 2 ^ 59
def prefixEnd_1754346 : Nat := 4983230072969 + 3 ^ 40 * 1754346 * 2
def baseEnd_1754346 : Nat := 200182829398377410423759

theorem tailTrace_1754346 : CollatzResearch.WordTrace tailWord_1754346 prefixEnd_1754346 200182829398377410423759 := by
  unfold tailWord_1754346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996563825577883822016723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42657503534874356858711261 15996563825577883822016723)
  ·
    refine ⟨23994845738366825733025085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15996563825577883822016723 23994845738366825733025085)
    ·
      refine ⟨8998067151887559649884407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23994845738366825733025085 8998067151887559649884407)
      ·
        refine ⟨13497100727831339474826611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8998067151887559649884407 13497100727831339474826611)
        ·
          refine ⟨20245651091747009212239917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13497100727831339474826611 20245651091747009212239917)
          ·
            refine ⟨7592119159405128454589969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20245651091747009212239917 7592119159405128454589969)
            ·
              refine ⟨5694089369553846340942477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592119159405128454589969 5694089369553846340942477)
              ·
                refine ⟨2135283513582692377853429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5694089369553846340942477 2135283513582692377853429)
                ·
                  refine ⟨200182829398377410423759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2135283513582692377853429 200182829398377410423759)
                  ·
                    rfl

theorem cell22_1754346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_1754346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754346 prefixEnd_1754346 := by exact prefixLift 1754346
  have htrace : WordTrace (prefixWord ++ tailWord_1754346) baseStart_1754346 baseEnd_1754346 := by
    simpa [prefixWord, tailWord_1754346, baseEnd_1754346] using wordTrace_append hprefix tailTrace_1754346
  have hstable : (prefixWord ++ tailWord_1754346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754346).length < 2 ^ (prefixWord ++ tailWord_1754346).sum := by decide
  have hdescent : baseEnd_1754346 < baseStart_1754346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754391 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 6]
def baseStart_1754391 : Nat := 118140960795 + 1754391 * 2 ^ 59
def prefixEnd_1754391 : Nat := 4983230072969 + 3 ^ 40 * 1754391 * 2
def baseEnd_1754391 : Nat := 200187964204922371298713

theorem tailTrace_1754391 : CollatzResearch.WordTrace tailWord_1754391 prefixEnd_1754391 200187964204922371298713 := by
  unfold tailWord_1754391
  simp only [CollatzResearch.WordTrace]
  refine ⟨63987896587148507973455027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42658597724765671982303351 63987896587148507973455027)
  ·
    refine ⟨95981844880722761960182541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63987896587148507973455027 95981844880722761960182541)
    ·
      refine ⟨35993191830271035735068453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95981844880722761960182541 35993191830271035735068453)
      ·
        refine ⟨6748723468175819200325335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35993191830271035735068453 6748723468175819200325335)
        ·
          refine ⟨10123085202263728800488003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748723468175819200325335 10123085202263728800488003)
          ·
            refine ⟨15184627803395593200732005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10123085202263728800488003 15184627803395593200732005)
            ·
              refine ⟨2847117713136673725137251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15184627803395593200732005 2847117713136673725137251)
              ·
                refine ⟨4270676569705010587705877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847117713136673725137251 4270676569705010587705877)
                ·
                  refine ⟨200187964204922371298713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4270676569705010587705877 200187964204922371298713)
                  ·
                    rfl

theorem cell22_1754391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 6].length) (baseStart_1754391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754391 prefixEnd_1754391 := by exact prefixLift 1754391
  have htrace : WordTrace (prefixWord ++ tailWord_1754391) baseStart_1754391 baseEnd_1754391 := by
    simpa [prefixWord, tailWord_1754391, baseEnd_1754391] using wordTrace_append hprefix tailTrace_1754391
  have hstable : (prefixWord ++ tailWord_1754391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754391).length < 2 ^ (prefixWord ++ tailWord_1754391).sum := by decide
  have hdescent : baseEnd_1754391 < baseStart_1754391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754410 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1754410 : Nat := 118140960795 + 1754410 * 2 ^ 59
def prefixEnd_1754410 : Nat := 4983230072969 + 3 ^ 40 * 1754410 * 2
def baseEnd_1754410 : Nat := 600570396703057397671081

theorem tailTrace_1754410 : CollatzResearch.WordTrace tailWord_1754410 prefixEnd_1754410 600570396703057397671081 := by
  unfold tailWord_1754410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15997147393519918554599171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42659059716053116145597789 15997147393519918554599171)
  ·
    refine ⟨23995721090279877831898757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15997147393519918554599171 23995721090279877831898757)
    ·
      refine ⟨4499197704427477093481017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23995721090279877831898757 4499197704427477093481017)
      ·
        refine ⟨3374398278320607820110763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4499197704427477093481017 3374398278320607820110763)
        ·
          refine ⟨5061597417480911730166145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374398278320607820110763 5061597417480911730166145)
          ·
            refine ⟨3796198063110683797624609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061597417480911730166145 3796198063110683797624609)
            ·
              refine ⟨2847148547333012848218457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796198063110683797624609 2847148547333012848218457)
              ·
                refine ⟨2135361410499759636163843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847148547333012848218457 2135361410499759636163843)
                ·
                  refine ⟨3203042115749639454245765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135361410499759636163843 3203042115749639454245765)
                  ·
                    refine ⟨600570396703057397671081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203042115749639454245765 600570396703057397671081)
                    ·
                      rfl

theorem cell22_1754410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1754410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754410 prefixEnd_1754410 := by exact prefixLift 1754410
  have htrace : WordTrace (prefixWord ++ tailWord_1754410) baseStart_1754410 baseEnd_1754410 := by
    simpa [prefixWord, tailWord_1754410, baseEnd_1754410] using wordTrace_append hprefix tailTrace_1754410
  have hstable : (prefixWord ++ tailWord_1754410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754410).length < 2 ^ (prefixWord ++ tailWord_1754410).sum := by decide
  have hdescent : baseEnd_1754410 < baseStart_1754410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754421 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1754421 : Nat := 118140960795 + 1754421 * 2 ^ 59
def prefixEnd_1754421 : Nat := 4983230072969 + 3 ^ 40 * 1754421 * 2
def baseEnd_1754421 : Nat := 600574162227857035646047

theorem tailTrace_1754421 : CollatzResearch.WordTrace tailWord_1754421 prefixEnd_1754421 600574162227857035646047 := by
  unfold tailWord_1754421
  simp only [CollatzResearch.WordTrace]
  refine ⟨63988990777039823097047117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42659327184693215398031411 63988990777039823097047117)
  ·
    refine ⟨23995871541389933661392669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63988990777039823097047117 23995871541389933661392669)
    ·
      refine ⟨8998451828021225123022251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23995871541389933661392669 8998451828021225123022251)
      ·
        refine ⟨13497677742031837684533377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8998451828021225123022251 13497677742031837684533377)
        ·
          refine ⟨10123258306523878263400033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13497677742031837684533377 10123258306523878263400033)
          ·
            refine ⟨7592443729892908697550025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123258306523878263400033 7592443729892908697550025)
            ·
              refine ⟨5694332797419681523162519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592443729892908697550025 5694332797419681523162519)
              ·
                refine ⟨8541499196129522284743779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5694332797419681523162519 8541499196129522284743779)
                ·
                  refine ⟨12812248794194283427115669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8541499196129522284743779 12812248794194283427115669)
                  ·
                    refine ⟨600574162227857035646047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12812248794194283427115669 600574162227857035646047)
                    ·
                      rfl

theorem cell22_1754421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1754421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754421 prefixEnd_1754421 := by exact prefixLift 1754421
  have htrace : WordTrace (prefixWord ++ tailWord_1754421) baseStart_1754421 baseEnd_1754421 := by
    simpa [prefixWord, tailWord_1754421, baseEnd_1754421] using wordTrace_append hprefix tailTrace_1754421
  have hstable : (prefixWord ++ tailWord_1754421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754421).length < 2 ^ (prefixWord ++ tailWord_1754421).sum := by decide
  have hdescent : baseEnd_1754421 < baseStart_1754421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754461 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1754461 : Nat := 118140960795 + 1754461 * 2 ^ 59
def prefixEnd_1754461 : Nat := 4983230072969 + 3 ^ 40 * 1754461 * 2
def baseEnd_1754461 : Nat := 600587855045310264645925

theorem tailTrace_1754461 : CollatzResearch.WordTrace tailWord_1754461 prefixEnd_1754461 600587855045310264645925 := by
  unfold tailWord_1754461
  simp only [CollatzResearch.WordTrace]
  refine ⟨63990449696894909928503237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42660299797929939952335491 63990449696894909928503237)
  ·
    refine ⟨11998209318167795611594357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63990449696894909928503237 11998209318167795611594357)
    ·
      refine ⟨1124832123578230838586971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11998209318167795611594357 1124832123578230838586971)
      ·
        refine ⟨1687248185367346257880457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124832123578230838586971 1687248185367346257880457)
        ·
          refine ⟨1265436139025509693410343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1687248185367346257880457 1265436139025509693410343)
          ·
            refine ⟨1898154208538264540115515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265436139025509693410343 1898154208538264540115515)
            ·
              refine ⟨2847231312807396810173273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898154208538264540115515 2847231312807396810173273)
              ·
                refine ⟨2135423484605547607629955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847231312807396810173273 2135423484605547607629955)
                ·
                  refine ⟨3203135226908321411444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135423484605547607629955 3203135226908321411444933)
                  ·
                    refine ⟨600587855045310264645925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203135226908321411444933 600587855045310264645925)
                    ·
                      rfl

theorem cell22_1754461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1754461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754461 prefixEnd_1754461 := by exact prefixLift 1754461
  have htrace : WordTrace (prefixWord ++ tailWord_1754461) baseStart_1754461 baseEnd_1754461 := by
    simpa [prefixWord, tailWord_1754461, baseEnd_1754461] using wordTrace_append hprefix tailTrace_1754461
  have hstable : (prefixWord ++ tailWord_1754461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754461).length < 2 ^ (prefixWord ++ tailWord_1754461).sum := by decide
  have hdescent : baseEnd_1754461 < baseStart_1754461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754528 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_1754528 : Nat := 118140960795 + 1754528 * 2 ^ 59
def prefixEnd_1754528 : Nat := 4983230072969 + 3 ^ 40 * 1754528 * 2
def baseEnd_1754528 : Nat := 600610790514544423220719

theorem tailTrace_1754528 : CollatzResearch.WordTrace tailWord_1754528 prefixEnd_1754528 600610790514544423220719 := by
  unfold tailWord_1754528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31996446693826090185596119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42661928925101453580794825 31996446693826090185596119)
  ·
    refine ⟨47994670040739135278394179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31996446693826090185596119 47994670040739135278394179)
    ·
      refine ⟨71992005061108702917591269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47994670040739135278394179 71992005061108702917591269)
      ·
        refine ⟨13498500948957881797048363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71992005061108702917591269 13498500948957881797048363)
        ·
          refine ⟨20247751423436822695572545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13498500948957881797048363 20247751423436822695572545)
          ·
            refine ⟨15185813567577617021679409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20247751423436822695572545 15185813567577617021679409)
            ·
              refine ⟨11389360175683212766259557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15185813567577617021679409 11389360175683212766259557)
              ·
                refine ⟨2135505032940602393673667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11389360175683212766259557 2135505032940602393673667)
                ·
                  refine ⟨3203257549410903590510501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2135505032940602393673667 3203257549410903590510501)
                  ·
                    refine ⟨600610790514544423220719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203257549410903590510501 600610790514544423220719)
                    ·
                      rfl

theorem cell22_1754528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_1754528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754528 prefixEnd_1754528 := by exact prefixLift 1754528
  have htrace : WordTrace (prefixWord ++ tailWord_1754528) baseStart_1754528 baseEnd_1754528 := by
    simpa [prefixWord, tailWord_1754528, baseEnd_1754528] using wordTrace_append hprefix tailTrace_1754528
  have hstable : (prefixWord ++ tailWord_1754528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754528).length < 2 ^ (prefixWord ++ tailWord_1754528).sum := by decide
  have hdescent : baseEnd_1754528 < baseStart_1754528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754605 : List Nat := [1, 5, 1, 3, 2, 2, 8]
def baseStart_1754605 : Nat := 118140960795 + 1754605 * 2 ^ 59
def prefixEnd_1754605 : Nat := 4983230072969 + 3 ^ 40 * 1754605 * 2
def baseEnd_1754605 : Nat := 22245820340301551446129

theorem tailTrace_1754605 : CollatzResearch.WordTrace tailWord_1754605 prefixEnd_1754605 22245820340301551446129 := by
  unfold tailWord_1754605
  simp only [CollatzResearch.WordTrace]
  refine ⟨63995701808373222521745269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42663801205582148347830179 63995701808373222521745269)
  ·
    refine ⟨5999597044534989611413619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63995701808373222521745269 5999597044534989611413619)
    ·
      refine ⟨8999395566802484417120429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5999597044534989611413619 8999395566802484417120429)
      ·
        refine ⟨3374773337550931656420161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8999395566802484417120429 3374773337550931656420161)
        ·
          refine ⟨2531080003163198742315121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3374773337550931656420161 2531080003163198742315121)
          ·
            refine ⟨1898310002372399056736341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531080003163198742315121 1898310002372399056736341)
            ·
              refine ⟨22245820340301551446129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1898310002372399056736341 22245820340301551446129)
              ·
                rfl

theorem cell22_1754605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 8].length) (baseStart_1754605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754605 prefixEnd_1754605 := by exact prefixLift 1754605
  have htrace : WordTrace (prefixWord ++ tailWord_1754605) baseStart_1754605 baseEnd_1754605 := by
    simpa [prefixWord, tailWord_1754605, baseEnd_1754605] using wordTrace_append hprefix tailTrace_1754605
  have hstable : (prefixWord ++ tailWord_1754605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754605).length < 2 ^ (prefixWord ++ tailWord_1754605).sum := by decide
  have hdescent : baseEnd_1754605 < baseStart_1754605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754620 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1754620 : Nat := 118140960795 + 1754620 * 2 ^ 59
def prefixEnd_1754620 : Nat := 4983230072969 + 3 ^ 40 * 1754620 * 2
def baseEnd_1754620 : Nat := 600642283994686849920437

theorem tailTrace_1754620 : CollatzResearch.WordTrace tailWord_1754620 prefixEnd_1754620 600642283994686849920437 := by
  unfold tailWord_1754620
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998124451659440041770657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42664165935545920055694209 31998124451659440041770657)
  ·
    refine ⟨23998593338744580031327993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31998124451659440041770657 23998593338744580031327993)
    ·
      refine ⟨17998945004058435023495995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23998593338744580031327993 17998945004058435023495995)
      ·
        refine ⟨26998417506087652535243993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17998945004058435023495995 26998417506087652535243993)
        ·
          refine ⟨20248813129565739401432995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26998417506087652535243993 20248813129565739401432995)
          ·
            refine ⟨30373219694348609102149493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20248813129565739401432995 30373219694348609102149493)
            ·
              refine ⟨2847489346345182103326515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30373219694348609102149493 2847489346345182103326515)
              ·
                refine ⟨4271234019517773154989773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847489346345182103326515 4271234019517773154989773)
                ·
                  refine ⟨1601712757319164933121165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4271234019517773154989773 1601712757319164933121165)
                  ·
                    refine ⟨600642283994686849920437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601712757319164933121165 600642283994686849920437)
                    ·
                      rfl

theorem cell22_1754620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1754620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754620 prefixEnd_1754620 := by exact prefixLift 1754620
  have htrace : WordTrace (prefixWord ++ tailWord_1754620) baseStart_1754620 baseEnd_1754620 := by
    simpa [prefixWord, tailWord_1754620, baseEnd_1754620] using wordTrace_append hprefix tailTrace_1754620
  have hstable : (prefixWord ++ tailWord_1754620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754620).length < 2 ^ (prefixWord ++ tailWord_1754620).sum := by decide
  have hdescent : baseEnd_1754620 < baseStart_1754620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754622 : List Nat := [4, 2, 2, 3, 1, 1, 2, 7]
def baseStart_1754622 : Nat := 118140960795 + 1754622 * 2 ^ 59
def prefixEnd_1754622 : Nat := 4983230072969 + 3 ^ 40 * 1754622 * 2
def baseEnd_1754622 : Nat := 66738107626173279041159

theorem tailTrace_1754622 : CollatzResearch.WordTrace tailWord_1754622 prefixEnd_1754622 66738107626173279041159 := by
  unfold tailWord_1754622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999540231163954303139265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42664214566207756283409413 7999540231163954303139265)
  ·
    refine ⟨5999655173372965727354449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7999540231163954303139265 5999655173372965727354449)
    ·
      refine ⟨4499741380029724295515837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5999655173372965727354449 4499741380029724295515837)
      ·
        refine ⟨1687403017511146610818439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4499741380029724295515837 1687403017511146610818439)
        ·
          refine ⟨2531104526266719916227659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687403017511146610818439 2531104526266719916227659)
          ·
            refine ⟨3796656789400079874341489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531104526266719916227659 3796656789400079874341489)
            ·
              refine ⟨2847492592050059905756117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796656789400079874341489 2847492592050059905756117)
              ·
                refine ⟨66738107626173279041159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2847492592050059905756117 66738107626173279041159)
                ·
                  rfl

theorem cell22_1754622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_1754622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754622 prefixEnd_1754622 := by exact prefixLift 1754622
  have htrace : WordTrace (prefixWord ++ tailWord_1754622) baseStart_1754622 baseEnd_1754622 := by
    simpa [prefixWord, tailWord_1754622, baseEnd_1754622] using wordTrace_append hprefix tailTrace_1754622
  have hstable : (prefixWord ++ tailWord_1754622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754622).length < 2 ^ (prefixWord ++ tailWord_1754622).sum := by decide
  have hdescent : baseEnd_1754622 < baseStart_1754622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754626 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1754626 : Nat := 118140960795 + 1754626 * 2 ^ 59
def prefixEnd_1754626 : Nat := 4983230072969 + 3 ^ 40 * 1754626 * 2
def baseEnd_1754626 : Nat := 600644337917304834270419

theorem tailTrace_1754626 : CollatzResearch.WordTrace tailWord_1754626 prefixEnd_1754626 600644337917304834270419 := by
  unfold tailWord_1754626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999116935324285777064933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42664311827531428738839821 15999116935324285777064933)
  ·
    refine ⟨2999834425373303583199675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15999116935324285777064933 2999834425373303583199675)
    ·
      refine ⟨4499751638059955374799513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2999834425373303583199675 4499751638059955374799513)
      ·
        refine ⟨3374813728544966531099635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4499751638059955374799513 3374813728544966531099635)
        ·
          refine ⟨5062220592817449796649453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374813728544966531099635 5062220592817449796649453)
          ·
            refine ⟨1898332722306543673743545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5062220592817449796649453 1898332722306543673743545)
            ·
              refine ⟨1423749541729907755307659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898332722306543673743545 1423749541729907755307659)
              ·
                refine ⟨2135624312594861632961489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423749541729907755307659 2135624312594861632961489)
                ·
                  refine ⟨1601718234446146224721117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135624312594861632961489 1601718234446146224721117)
                  ·
                    refine ⟨600644337917304834270419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601718234446146224721117 600644337917304834270419)
                    ·
                      rfl

theorem cell22_1754626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1754626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754626 prefixEnd_1754626 := by exact prefixLift 1754626
  have htrace : WordTrace (prefixWord ++ tailWord_1754626) baseStart_1754626 baseEnd_1754626 := by
    simpa [prefixWord, tailWord_1754626, baseEnd_1754626] using wordTrace_append hprefix tailTrace_1754626
  have hstable : (prefixWord ++ tailWord_1754626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754626).length < 2 ^ (prefixWord ++ tailWord_1754626).sum := by decide
  have hdescent : baseEnd_1754626 < baseStart_1754626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754633 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 5]
def baseStart_1754633 : Nat := 118140960795 + 1754633 * 2 ^ 59
def prefixEnd_1754633 : Nat := 4983230072969 + 3 ^ 40 * 1754633 * 2
def baseEnd_1754633 : Nat := 200215578053453049781799

theorem tailTrace_1754633 : CollatzResearch.WordTrace tailWord_1754633 prefixEnd_1754633 200215578053453049781799 := by
  unfold tailWord_1754633
  simp only [CollatzResearch.WordTrace]
  refine ⟨63996723052271783303764553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42664482034847855535843035 63996723052271783303764553)
  ·
    refine ⟨47997542289203837477823415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63996723052271783303764553 47997542289203837477823415)
    ·
      refine ⟨71996313433805756216735123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47997542289203837477823415 71996313433805756216735123)
      ·
        refine ⟨107994470150708634325102685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71996313433805756216735123 107994470150708634325102685)
        ·
          refine ⟨40497926306515737871913507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107994470150708634325102685 40497926306515737871913507)
          ·
            refine ⟨60746889459773606807870261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40497926306515737871913507 60746889459773606807870261)
            ·
              refine ⟨5695020886853775638237837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60746889459773606807870261 5695020886853775638237837)
              ·
                refine ⟨2135632832570165864339189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5695020886853775638237837 2135632832570165864339189)
                ·
                  refine ⟨200215578053453049781799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2135632832570165864339189 200215578053453049781799)
                  ·
                    rfl

theorem cell22_1754633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 5].length) (baseStart_1754633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754633 prefixEnd_1754633 := by exact prefixLift 1754633
  have htrace : WordTrace (prefixWord ++ tailWord_1754633) baseStart_1754633 baseEnd_1754633 := by
    simpa [prefixWord, tailWord_1754633, baseEnd_1754633] using wordTrace_append hprefix tailTrace_1754633
  have hstable : (prefixWord ++ tailWord_1754633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754633).length < 2 ^ (prefixWord ++ tailWord_1754633).sum := by decide
  have hdescent : baseEnd_1754633 < baseStart_1754633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754695 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 6]
def baseStart_1754695 : Nat := 118140960795 + 1754695 * 2 ^ 59
def prefixEnd_1754695 : Nat := 4983230072969 + 3 ^ 40 * 1754695 * 2
def baseEnd_1754695 : Nat := 200222652675803884765069

theorem tailTrace_1754695 : CollatzResearch.WordTrace tailWord_1754695 prefixEnd_1754695 200222652675803884765069 := by
  unfold tailWord_1754695
  simp only [CollatzResearch.WordTrace]
  refine ⟨63998984378047167892521539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42665989585364778595014359 63998984378047167892521539)
  ·
    refine ⟨95998476567070751838782309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63998984378047167892521539 95998476567070751838782309)
    ·
      refine ⟨17999714356325765969771683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95998476567070751838782309 17999714356325765969771683)
      ·
        refine ⟨26999571534488648954657525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17999714356325765969771683 26999571534488648954657525)
        ·
          refine ⟨2531209831358310839499143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26999571534488648954657525 2531209831358310839499143)
          ·
            refine ⟨3796814747037466259248715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531209831358310839499143 3796814747037466259248715)
            ·
              refine ⟨5695222120556199388873073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3796814747037466259248715 5695222120556199388873073)
              ·
                refine ⟨4271416590417149541654805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5695222120556199388873073 4271416590417149541654805)
                ·
                  refine ⟨200222652675803884765069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4271416590417149541654805 200222652675803884765069)
                  ·
                    rfl

theorem cell22_1754695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 6].length) (baseStart_1754695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754695 prefixEnd_1754695 := by exact prefixLift 1754695
  have htrace : WordTrace (prefixWord ++ tailWord_1754695) baseStart_1754695 baseEnd_1754695 := by
    simpa [prefixWord, tailWord_1754695, baseEnd_1754695] using wordTrace_append hprefix tailTrace_1754695
  have hstable : (prefixWord ++ tailWord_1754695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754695).length < 2 ^ (prefixWord ++ tailWord_1754695).sum := by decide
  have hdescent : baseEnd_1754695 < baseStart_1754695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754723 : List Nat := [1, 1, 1, 5, 1, 4, 9]
def baseStart_1754723 : Nat := 118140960795 + 1754723 * 2 ^ 59
def prefixEnd_1754723 : Nat := 4983230072969 + 3 ^ 40 * 1754723 * 2
def baseEnd_1754723 : Nat := 22247316407393663503523

theorem tailTrace_1754723 : CollatzResearch.WordTrace tailWord_1754723 prefixEnd_1754723 22247316407393663503523 := by
  unfold tailWord_1754723
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000005621945728674540823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42666670414630485783027215 64000005621945728674540823)
  ·
    refine ⟨96000008432918593011811235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64000005621945728674540823 96000008432918593011811235)
    ·
      refine ⟨144000012649377889517716853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96000008432918593011811235 144000012649377889517716853)
      ·
        refine ⟨13500001185879177142285955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144000012649377889517716853 13500001185879177142285955)
        ·
          refine ⟨20250001778818765713428933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13500001185879177142285955 20250001778818765713428933)
          ·
            refine ⟨3796875333528518571267925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20250001778818765713428933 3796875333528518571267925)
            ·
              refine ⟨22247316407393663503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3796875333528518571267925 22247316407393663503523)
              ·
                rfl

theorem cell22_1754723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 9].length) (baseStart_1754723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754723 prefixEnd_1754723 := by exact prefixLift 1754723
  have htrace : WordTrace (prefixWord ++ tailWord_1754723) baseStart_1754723 baseEnd_1754723 := by
    simpa [prefixWord, tailWord_1754723, baseEnd_1754723] using wordTrace_append hprefix tailTrace_1754723
  have hstable : (prefixWord ++ tailWord_1754723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754723).length < 2 ^ (prefixWord ++ tailWord_1754723).sum := by decide
  have hdescent : baseEnd_1754723 < baseStart_1754723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754727 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1754727 : Nat := 118140960795 + 1754727 * 2 ^ 59
def prefixEnd_1754727 : Nat := 4983230072969 + 3 ^ 40 * 1754727 * 2
def baseEnd_1754727 : Nat := 600678912281374237495109

theorem tailTrace_1754727 : CollatzResearch.WordTrace tailWord_1754727 prefixEnd_1754727 600678912281374237495109 := by
  unfold tailWord_1754727
  simp only [CollatzResearch.WordTrace]
  refine ⟨64000151513931237357686435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42666767675954158238457623 64000151513931237357686435)
  ·
    refine ⟨96000227270896856036529653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64000151513931237357686435 96000227270896856036529653)
    ·
      refine ⟨9000021306646580253424655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96000227270896856036529653 9000021306646580253424655)
      ·
        refine ⟨13500031959969870380136983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000021306646580253424655 13500031959969870380136983)
        ·
          refine ⟨20250047939954805570205475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13500031959969870380136983 20250047939954805570205475)
          ·
            refine ⟨30375071909932208355308213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20250047939954805570205475 30375071909932208355308213)
            ·
              refine ⟨2847662991556144533310145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30375071909932208355308213 2847662991556144533310145)
              ·
                refine ⟨2135747243667108399982609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847662991556144533310145 2135747243667108399982609)
                ·
                  refine ⟨1601810432750331299986957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135747243667108399982609 1601810432750331299986957)
                  ·
                    refine ⟨600678912281374237495109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1601810432750331299986957 600678912281374237495109)
                    ·
                      rfl

theorem cell22_1754727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1754727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754727 prefixEnd_1754727 := by exact prefixLift 1754727
  have htrace : WordTrace (prefixWord ++ tailWord_1754727) baseStart_1754727 baseEnd_1754727 := by
    simpa [prefixWord, tailWord_1754727, baseEnd_1754727] using wordTrace_append hprefix tailTrace_1754727
  have hstable : (prefixWord ++ tailWord_1754727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754727).length < 2 ^ (prefixWord ++ tailWord_1754727).sum := by decide
  have hdescent : baseEnd_1754727 < baseStart_1754727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754785 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 7]
def baseStart_1754785 : Nat := 118140960795 + 1754785 * 2 ^ 59
def prefixEnd_1754785 : Nat := 4983230072969 + 3 ^ 40 * 1754785 * 2
def baseEnd_1754785 : Nat := 200232922288893806514977

theorem tailTrace_1754785 : CollatzResearch.WordTrace tailWord_1754785 prefixEnd_1754785 200232922288893806514977 := by
  unfold tailWord_1754785
  simp only [CollatzResearch.WordTrace]
  refine ⟨64002266947721113263297809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42668177965147408842198539 64002266947721113263297809)
  ·
    refine ⟨48001700210790834947473357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64002266947721113263297809 48001700210790834947473357)
    ·
      refine ⟨18000637579046563105302509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48001700210790834947473357 18000637579046563105302509)
      ·
        refine ⟨6750239092142461164488441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18000637579046563105302509 6750239092142461164488441)
        ·
          refine ⟨5062679319106845873366331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6750239092142461164488441 5062679319106845873366331)
          ·
            refine ⟨7594018978660268810049497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062679319106845873366331 7594018978660268810049497)
            ·
              refine ⟨5695514233995201607537123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7594018978660268810049497 5695514233995201607537123)
              ·
                refine ⟨8543271350992802411305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695514233995201607537123 8543271350992802411305685)
                ·
                  refine ⟨200232922288893806514977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8543271350992802411305685 200232922288893806514977)
                  ·
                    rfl

theorem cell22_1754785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_1754785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754785 prefixEnd_1754785 := by exact prefixLift 1754785
  have htrace : WordTrace (prefixWord ++ tailWord_1754785) baseStart_1754785 baseEnd_1754785 := by
    simpa [prefixWord, tailWord_1754785, baseEnd_1754785] using wordTrace_append hprefix tailTrace_1754785
  have hstable : (prefixWord ++ tailWord_1754785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754785).length < 2 ^ (prefixWord ++ tailWord_1754785).sum := by decide
  have hdescent : baseEnd_1754785 < baseStart_1754785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754802 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_1754802 : Nat := 118140960795 + 1754802 * 2 ^ 59
def prefixEnd_1754802 : Nat := 4983230072969 + 3 ^ 40 * 1754802 * 2
def baseEnd_1754802 : Nat := 200234862104699680623293

theorem tailTrace_1754802 : CollatzResearch.WordTrace tailWord_1754802 prefixEnd_1754802 200234862104699680623293 := by
  unfold tailWord_1754802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16000721747164881291666665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42668591325773016777777773 16000721747164881291666665)
  ·
    refine ⟨12000541310373660968749999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16000721747164881291666665 12000541310373660968749999)
    ·
      refine ⟨18000811965560491453124999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12000541310373660968749999 18000811965560491453124999)
      ·
        refine ⟨27001217948340737179687499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18000811965560491453124999 27001217948340737179687499)
        ·
          refine ⟨40501826922511105769531249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27001217948340737179687499 40501826922511105769531249)
          ·
            refine ⟨30376370191883329327148437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40501826922511105769531249 30376370191883329327148437)
            ·
              refine ⟨1423892352744531062210083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30376370191883329327148437 1423892352744531062210083)
              ·
                refine ⟨2135838529116796593315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423892352744531062210083 2135838529116796593315125)
                ·
                  refine ⟨200234862104699680623293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2135838529116796593315125 200234862104699680623293)
                  ·
                    rfl

theorem cell22_1754802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_1754802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754802 prefixEnd_1754802 := by exact prefixLift 1754802
  have htrace : WordTrace (prefixWord ++ tailWord_1754802) baseStart_1754802 baseEnd_1754802 := by
    simpa [prefixWord, tailWord_1754802, baseEnd_1754802] using wordTrace_append hprefix tailTrace_1754802
  have hstable : (prefixWord ++ tailWord_1754802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754802).length < 2 ^ (prefixWord ++ tailWord_1754802).sum := by decide
  have hdescent : baseEnd_1754802 < baseStart_1754802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754815 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_1754815 : Nat := 118140960795 + 1754815 * 2 ^ 59
def prefixEnd_1754815 : Nat := 4983230072969 + 3 ^ 40 * 1754815 * 2
def baseEnd_1754815 : Nat := 600709036479771341294839

theorem tailTrace_1754815 : CollatzResearch.WordTrace tailWord_1754815 prefixEnd_1754815 600709036479771341294839 := by
  unfold tailWord_1754815
  simp only [CollatzResearch.WordTrace]
  refine ⟨64003361137612428386889899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42668907425074952257926599 64003361137612428386889899)
  ·
    refine ⟨96005041706418642580334849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64003361137612428386889899 96005041706418642580334849)
    ·
      refine ⟨72003781279813981935251137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96005041706418642580334849 72003781279813981935251137)
      ·
        refine ⟨54002835959860486451438353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72003781279813981935251137 54002835959860486451438353)
        ·
          refine ⟨40502126969895364838578765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54002835959860486451438353 40502126969895364838578765)
          ·
            refine ⟨15188297613710761814467037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40502126969895364838578765 15188297613710761814467037)
            ·
              refine ⟨5695611605141535680425139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15188297613710761814467037 5695611605141535680425139)
              ·
                refine ⟨8543417407712303520637709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5695611605141535680425139 8543417407712303520637709)
                ·
                  refine ⟨3203781527892113820239141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8543417407712303520637709 3203781527892113820239141)
                  ·
                    refine ⟨600709036479771341294839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203781527892113820239141 600709036479771341294839)
                    ·
                      rfl

theorem cell22_1754815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_1754815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754815 prefixEnd_1754815 := by exact prefixLift 1754815
  have htrace : WordTrace (prefixWord ++ tailWord_1754815) baseStart_1754815 baseEnd_1754815 := by
    simpa [prefixWord, tailWord_1754815, baseEnd_1754815] using wordTrace_append hprefix tailTrace_1754815
  have hstable : (prefixWord ++ tailWord_1754815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754815).length < 2 ^ (prefixWord ++ tailWord_1754815).sum := by decide
  have hdescent : baseEnd_1754815 < baseStart_1754815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754847 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 4]
def baseStart_1754847 : Nat := 118140960795 + 1754847 * 2 ^ 59
def prefixEnd_1754847 : Nat := 4983230072969 + 3 ^ 40 * 1754847 * 2
def baseEnd_1754847 : Nat := 200239996911244641498247

theorem tailTrace_1754847 : CollatzResearch.WordTrace tailWord_1754847 prefixEnd_1754847 200239996911244641498247 := by
  unfold tailWord_1754847
  simp only [CollatzResearch.WordTrace]
  refine ⟨64004528273496497852054795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42669685515664331901369863 64004528273496497852054795)
  ·
    refine ⟨96006792410244746778082193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64004528273496497852054795 96006792410244746778082193)
    ·
      refine ⟨72005094307683560083561645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96006792410244746778082193 72005094307683560083561645)
      ·
        refine ⟨27001910365381335031335617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72005094307683560083561645 27001910365381335031335617)
        ·
          refine ⟨20251432774036001273501713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27001910365381335031335617 20251432774036001273501713)
          ·
            refine ⟨15188574580527000955126285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20251432774036001273501713 15188574580527000955126285)
            ·
              refine ⟨5695715467697625358172357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15188574580527000955126285 5695715467697625358172357)
              ·
                refine ⟨1067946650193304754657317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5695715467697625358172357 1067946650193304754657317)
                ·
                  refine ⟨200239996911244641498247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067946650193304754657317 200239996911244641498247)
                  ·
                    rfl

theorem cell22_1754847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 4].length) (baseStart_1754847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754847 prefixEnd_1754847 := by exact prefixLift 1754847
  have htrace : WordTrace (prefixWord ++ tailWord_1754847) baseStart_1754847 baseEnd_1754847 := by
    simpa [prefixWord, tailWord_1754847, baseEnd_1754847] using wordTrace_append hprefix tailTrace_1754847
  have hstable : (prefixWord ++ tailWord_1754847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754847).length < 2 ^ (prefixWord ++ tailWord_1754847).sum := by decide
  have hdescent : baseEnd_1754847 < baseStart_1754847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754860 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1754860 : Nat := 118140960795 + 1754860 * 2 ^ 59
def prefixEnd_1754860 : Nat := 4983230072969 + 3 ^ 40 * 1754860 * 2
def baseEnd_1754860 : Nat := 600724440899406223919701

theorem tailTrace_1754860 : CollatzResearch.WordTrace tailWord_1754860 prefixEnd_1754860 600724440899406223919701 := by
  unfold tailWord_1754860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32002501211224700536139017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42670001614966267381518689 32002501211224700536139017)
  ·
    refine ⟨24001875908418525402104263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32002501211224700536139017 24001875908418525402104263)
    ·
      refine ⟨36002813862627788103156395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24001875908418525402104263 36002813862627788103156395)
      ·
        refine ⟨54004220793941682154734593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36002813862627788103156395 54004220793941682154734593)
        ·
          refine ⟨40503165595456261616050945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54004220793941682154734593 40503165595456261616050945)
          ·
            refine ⟨30377374196592196212038209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40503165595456261616050945 30377374196592196212038209)
            ·
              refine ⟨22783030647444147159028657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30377374196592196212038209 22783030647444147159028657)
              ·
                refine ⟨17087272985583110369271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22783030647444147159028657 17087272985583110369271493)
                ·
                  refine ⟨3203863684796833194238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17087272985583110369271493 3203863684796833194238405)
                  ·
                    refine ⟨600724440899406223919701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3203863684796833194238405 600724440899406223919701)
                    ·
                      rfl

theorem cell22_1754860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1754860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754860 prefixEnd_1754860 := by exact prefixLift 1754860
  have htrace : WordTrace (prefixWord ++ tailWord_1754860) baseStart_1754860 baseEnd_1754860 := by
    simpa [prefixWord, tailWord_1754860, baseEnd_1754860] using wordTrace_append hprefix tailTrace_1754860
  have hstable : (prefixWord ++ tailWord_1754860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754860).length < 2 ^ (prefixWord ++ tailWord_1754860).sum := by decide
  have hdescent : baseEnd_1754860 < baseStart_1754860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754862 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1754862 : Nat := 118140960795 + 1754862 * 2 ^ 59
def prefixEnd_1754862 : Nat := 4983230072969 + 3 ^ 40 * 1754862 * 2
def baseEnd_1754862 : Nat := 600725125540278885369695

theorem tailTrace_1754862 : CollatzResearch.WordTrace tailWord_1754862 prefixEnd_1754862 600725125540278885369695 := by
  unfold tailWord_1754862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000634421055269426731355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42670050245628103609233893 8000634421055269426731355)
  ·
    refine ⟨12000951631582904140097033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000634421055269426731355 12000951631582904140097033)
    ·
      refine ⟨9000713723687178105072775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12000951631582904140097033 9000713723687178105072775)
      ·
        refine ⟨13501070585530767157609163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000713723687178105072775 13501070585530767157609163)
        ·
          refine ⟨20251605878296150736413745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13501070585530767157609163 20251605878296150736413745)
          ·
            refine ⟨15188704408722113052310309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20251605878296150736413745 15188704408722113052310309)
            ·
              refine ⟨2847882076635396197308183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15188704408722113052310309 2847882076635396197308183)
              ·
                refine ⟨4271823114953094295962275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2847882076635396197308183 4271823114953094295962275)
                ·
                  refine ⟨6407734672429641443943413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4271823114953094295962275 6407734672429641443943413)
                  ·
                    refine ⟨600725125540278885369695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6407734672429641443943413 600725125540278885369695)
                    ·
                      rfl

theorem cell22_1754862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1754862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754862 prefixEnd_1754862 := by exact prefixLift 1754862
  have htrace : WordTrace (prefixWord ++ tailWord_1754862) baseStart_1754862 baseEnd_1754862 := by
    simpa [prefixWord, tailWord_1754862, baseEnd_1754862] using wordTrace_append hprefix tailTrace_1754862
  have hstable : (prefixWord ++ tailWord_1754862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754862).length < 2 ^ (prefixWord ++ tailWord_1754862).sum := by decide
  have hdescent : baseEnd_1754862 < baseStart_1754862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754926 : List Nat := [4, 1, 3, 2, 2, 2, 2, 6]
def baseStart_1754926 : Nat := 118140960795 + 1754926 * 2 ^ 59
def prefixEnd_1754926 : Nat := 4983230072969 + 3 ^ 40 * 1754926 * 2
def baseEnd_1754926 : Nat := 66749670449800450196611

theorem tailTrace_1754926 : CollatzResearch.WordTrace tailWord_1754926 prefixEnd_1754926 66749670449800450196611 := by
  unfold tailWord_1754926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000926205026286793022579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42671606426806862896120421 8000926205026286793022579)
  ·
    refine ⟨12001389307539430189533869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000926205026286793022579 12001389307539430189533869)
    ·
      refine ⟨4500520990327286321075201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12001389307539430189533869 4500520990327286321075201)
      ·
        refine ⟨3375390742745464740806401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500520990327286321075201 3375390742745464740806401)
        ·
          refine ⟨2531543057059098555604801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3375390742745464740806401 2531543057059098555604801)
          ·
            refine ⟨1898657292794323916703601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531543057059098555604801 1898657292794323916703601)
            ·
              refine ⟨1423992969595742937527701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898657292794323916703601 1423992969595742937527701)
              ·
                refine ⟨66749670449800450196611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1423992969595742937527701 66749670449800450196611)
                ·
                  rfl

theorem cell22_1754926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_1754926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754926 prefixEnd_1754926 := by exact prefixLift 1754926
  have htrace : WordTrace (prefixWord ++ tailWord_1754926) baseStart_1754926 baseEnd_1754926 := by
    simpa [prefixWord, tailWord_1754926, baseEnd_1754926] using wordTrace_append hprefix tailTrace_1754926
  have hstable : (prefixWord ++ tailWord_1754926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754926).length < 2 ^ (prefixWord ++ tailWord_1754926).sum := by decide
  have hdescent : baseEnd_1754926 < baseStart_1754926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754935 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1754935 : Nat := 118140960795 + 1754935 * 2 ^ 59
def prefixEnd_1754935 : Nat := 4983230072969 + 3 ^ 40 * 1754935 * 2
def baseEnd_1754935 : Nat := 600750114932131028294471

theorem tailTrace_1754935 : CollatzResearch.WordTrace tailWord_1754935 prefixEnd_1754935 600750114932131028294471 := by
  unfold tailWord_1754935
  simp only [CollatzResearch.WordTrace]
  refine ⟨64007737897177688881258259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42671825264785125920838839 64007737897177688881258259)
  ·
    refine ⟨96011606845766533321887389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64007737897177688881258259 96011606845766533321887389)
    ·
      refine ⟨36004352567162449995707771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96011606845766533321887389 36004352567162449995707771)
      ·
        refine ⟨54006528850743674993561657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36004352567162449995707771 54006528850743674993561657)
        ·
          refine ⟨40504896638057756245171243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54006528850743674993561657 40504896638057756245171243)
          ·
            refine ⟨60757344957086634367756865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40504896638057756245171243 60757344957086634367756865)
            ·
              refine ⟨45568008717814975775817649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60757344957086634367756865 45568008717814975775817649)
              ·
                refine ⟨34176006538361231831863237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45568008717814975775817649 34176006538361231831863237)
                ·
                  refine ⟨6408001225942730968474357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34176006538361231831863237 6408001225942730968474357)
                  ·
                    refine ⟨600750114932131028294471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6408001225942730968474357 600750114932131028294471)
                    ·
                      rfl

theorem cell22_1754935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1754935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1754935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1754935 prefixEnd_1754935 := by exact prefixLift 1754935
  have htrace : WordTrace (prefixWord ++ tailWord_1754935) baseStart_1754935 baseEnd_1754935 := by
    simpa [prefixWord, tailWord_1754935, baseEnd_1754935] using wordTrace_append hprefix tailTrace_1754935
  have hstable : (prefixWord ++ tailWord_1754935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754935).length < 2 ^ (prefixWord ++ tailWord_1754935).sum := by decide
  have hdescent : baseEnd_1754935 < baseStart_1754935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755016 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_1755016 : Nat := 118140960795 + 1755016 * 2 ^ 59
def prefixEnd_1755016 : Nat := 4983230072969 + 3 ^ 40 * 1755016 * 2
def baseEnd_1755016 : Nat := 200259280962491272339741

theorem tailTrace_1755016 : CollatzResearch.WordTrace tailWord_1755016 prefixEnd_1755016 200259280962491272339741 := by
  unfold tailWord_1755016
  simp only [CollatzResearch.WordTrace]
  refine ⟨32005346104942119857478451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42673794806589493143304601 32005346104942119857478451)
  ·
    refine ⟨48008019157413179786217677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32005346104942119857478451 48008019157413179786217677)
    ·
      refine ⟨18003007184029942419831629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48008019157413179786217677 18003007184029942419831629)
      ·
        refine ⟨6751127694011228407436861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18003007184029942419831629 6751127694011228407436861)
        ·
          refine ⟨2531672885254210652788823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6751127694011228407436861 2531672885254210652788823)
          ·
            refine ⟨3797509327881315979183235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531672885254210652788823 3797509327881315979183235)
            ·
              refine ⟨5696263991821973968774853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797509327881315979183235 5696263991821973968774853)
              ·
                refine ⟨1068049498466620119145285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5696263991821973968774853 1068049498466620119145285)
                ·
                  refine ⟨200259280962491272339741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068049498466620119145285 200259280962491272339741)
                  ·
                    rfl

theorem cell22_1755016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_1755016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755016 prefixEnd_1755016 := by exact prefixLift 1755016
  have htrace : WordTrace (prefixWord ++ tailWord_1755016) baseStart_1755016 baseEnd_1755016 := by
    simpa [prefixWord, tailWord_1755016, baseEnd_1755016] using wordTrace_append hprefix tailTrace_1755016
  have hstable : (prefixWord ++ tailWord_1755016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755016).length < 2 ^ (prefixWord ++ tailWord_1755016).sum := by decide
  have hdescent : baseEnd_1755016 < baseStart_1755016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755044 : List Nat := [2, 3, 1, 2, 1, 4, 3, 6]
def baseStart_1755044 : Nat := 118140960795 + 1755044 * 2 ^ 59
def prefixEnd_1755044 : Nat := 4983230072969 + 3 ^ 40 * 1755044 * 2
def baseEnd_1755044 : Nat := 66754158651076786368793

theorem tailTrace_1755044 : CollatzResearch.WordTrace tailWord_1755044 prefixEnd_1755044 66754158651076786368793 := by
  unfold tailWord_1755044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32005856726891400248488093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42674475635855200331317457 32005856726891400248488093)
  ·
    refine ⟨12002196272584275093183035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32005856726891400248488093 12002196272584275093183035)
    ·
      refine ⟨18003294408876412639774553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002196272584275093183035 18003294408876412639774553)
      ·
        refine ⟨13502470806657309479830915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18003294408876412639774553 13502470806657309479830915)
        ·
          refine ⟨20253706209985964219746373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13502470806657309479830915 20253706209985964219746373)
          ·
            refine ⟨3797569914372368291202445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20253706209985964219746373 3797569914372368291202445)
            ·
              refine ⟨1424088717889638109200917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3797569914372368291202445 1424088717889638109200917)
              ·
                refine ⟨66754158651076786368793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1424088717889638109200917 66754158651076786368793)
                ·
                  rfl

theorem cell22_1755044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_1755044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755044 prefixEnd_1755044 := by exact prefixLift 1755044
  have htrace : WordTrace (prefixWord ++ tailWord_1755044) baseStart_1755044 baseEnd_1755044 := by
    simpa [prefixWord, tailWord_1755044, baseEnd_1755044] using wordTrace_append hprefix tailTrace_1755044
  have hstable : (prefixWord ++ tailWord_1755044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755044).length < 2 ^ (prefixWord ++ tailWord_1755044).sum := by decide
  have hdescent : baseEnd_1755044 < baseStart_1755044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755072 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_1755072 : Nat := 118140960795 + 1755072 * 2 ^ 59
def prefixEnd_1755072 : Nat := 4983230072969 + 3 ^ 40 * 1755072 * 2
def baseEnd_1755072 : Nat := 200265670943969445873017

theorem tailTrace_1755072 : CollatzResearch.WordTrace tailWord_1755072 prefixEnd_1755072 200265670943969445873017 := by
  unfold tailWord_1755072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32006367348840680639497735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42675156465120907519330313 32006367348840680639497735)
  ·
    refine ⟨48009551023261020959246603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32006367348840680639497735 48009551023261020959246603)
    ·
      refine ⟨72014326534891531438869905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48009551023261020959246603 72014326534891531438869905)
      ·
        refine ⟨54010744901168648579152429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72014326534891531438869905 54010744901168648579152429)
        ·
          refine ⟨20254029337938243217182161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54010744901168648579152429 20254029337938243217182161)
          ·
            refine ⟨15190522003453682412886621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20254029337938243217182161 15190522003453682412886621)
            ·
              refine ⟨5696445751295130904832483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15190522003453682412886621 5696445751295130904832483)
              ·
                refine ⟨8544668626942696357248725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696445751295130904832483 8544668626942696357248725)
                ·
                  refine ⟨200265670943969445873017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8544668626942696357248725 200265670943969445873017)
                  ·
                    rfl

theorem cell22_1755072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_1755072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755072 prefixEnd_1755072 := by exact prefixLift 1755072
  have htrace : WordTrace (prefixWord ++ tailWord_1755072) baseStart_1755072 baseEnd_1755072 := by
    simpa [prefixWord, tailWord_1755072, baseEnd_1755072] using wordTrace_append hprefix tailTrace_1755072
  have hstable : (prefixWord ++ tailWord_1755072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755072).length < 2 ^ (prefixWord ++ tailWord_1755072).sum := by decide
  have hdescent : baseEnd_1755072 < baseStart_1755072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755087 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_1755087 : Nat := 118140960795 + 1755087 * 2 ^ 59
def prefixEnd_1755087 : Nat := 4983230072969 + 3 ^ 40 * 1755087 * 2
def baseEnd_1755087 : Nat := 600802147638453298494005

theorem tailTrace_1755087 : CollatzResearch.WordTrace tailWord_1755087 prefixEnd_1755087 600802147638453298494005 := by
  unfold tailWord_1755087
  simp only [CollatzResearch.WordTrace]
  refine ⟨64013281792627018840791515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42675521195084679227194343 64013281792627018840791515)
  ·
    refine ⟨96019922688940528261187273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64013281792627018840791515 96019922688940528261187273)
    ·
      refine ⟨72014942016705396195890455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96019922688940528261187273 72014942016705396195890455)
      ·
        refine ⟨108022413025058094293835683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72014942016705396195890455 108022413025058094293835683)
        ·
          refine ⟨162033619537587141440753525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108022413025058094293835683 162033619537587141440753525)
          ·
            refine ⟨15190651831648794510070643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162033619537587141440753525 15190651831648794510070643)
            ·
              refine ⟨22785977747473191765105965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190651831648794510070643 22785977747473191765105965)
              ·
                refine ⟨8544741655302446911914737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22785977747473191765105965 8544741655302446911914737)
                ·
                  refine ⟨6408556241476835183936053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8544741655302446911914737 6408556241476835183936053)
                  ·
                    refine ⟨600802147638453298494005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6408556241476835183936053 600802147638453298494005)
                    ·
                      rfl

theorem cell22_1755087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_1755087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755087 prefixEnd_1755087 := by exact prefixLift 1755087
  have htrace : WordTrace (prefixWord ++ tailWord_1755087) baseStart_1755087 baseEnd_1755087 := by
    simpa [prefixWord, tailWord_1755087, baseEnd_1755087] using wordTrace_append hprefix tailTrace_1755087
  have hstable : (prefixWord ++ tailWord_1755087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755087).length < 2 ^ (prefixWord ++ tailWord_1755087).sum := by decide
  have hdescent : baseEnd_1755087 < baseStart_1755087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755119 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 1, 4]
def baseStart_1755119 : Nat := 118140960795 + 1755119 * 2 ^ 59
def prefixEnd_1755119 : Nat := 4983230072969 + 3 ^ 40 * 1755119 * 2
def baseEnd_1755119 : Nat := 600813101892415881693907

theorem tailTrace_1755119 : CollatzResearch.WordTrace tailWord_1755119 prefixEnd_1755119 600813101892415881693907 := by
  unfold tailWord_1755119
  simp only [CollatzResearch.WordTrace]
  refine ⟨64014448928511088305956411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42676299285674058870637607 64014448928511088305956411)
  ·
    refine ⟨96021673392766632458934617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64014448928511088305956411 96021673392766632458934617)
    ·
      refine ⟨72016255044574974344200963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96021673392766632458934617 72016255044574974344200963)
      ·
        refine ⟨108024382566862461516301445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72016255044574974344200963 108024382566862461516301445)
        ·
          refine ⟨20254571731286711534306521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108024382566862461516301445 20254571731286711534306521)
          ·
            refine ⟨15190928798465033650729891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20254571731286711534306521 15190928798465033650729891)
            ·
              refine ⟨22786393197697550476094837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15190928798465033650729891 22786393197697550476094837)
              ·
                refine ⟨2136224362284145357133891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22786393197697550476094837 2136224362284145357133891)
                ·
                  refine ⟨3204336543426218035700837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136224362284145357133891 3204336543426218035700837)
                  ·
                    refine ⟨600813101892415881693907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204336543426218035700837 600813101892415881693907)
                    ·
                      rfl

theorem cell22_1755119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_1755119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755119 prefixEnd_1755119 := by exact prefixLift 1755119
  have htrace : WordTrace (prefixWord ++ tailWord_1755119) baseStart_1755119 baseEnd_1755119 := by
    simpa [prefixWord, tailWord_1755119, baseEnd_1755119] using wordTrace_append hprefix tailTrace_1755119
  have hstable : (prefixWord ++ tailWord_1755119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755119).length < 2 ^ (prefixWord ++ tailWord_1755119).sum := by decide
  have hdescent : baseEnd_1755119 < baseStart_1755119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755140 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_1755140 : Nat := 118140960795 + 1755140 * 2 ^ 59
def prefixEnd_1755140 : Nat := 4983230072969 + 3 ^ 40 * 1755140 * 2
def baseEnd_1755140 : Nat := 200273430207192942306281

theorem tailTrace_1755140 : CollatzResearch.WordTrace tailWord_1755140 prefixEnd_1755140 200273430207192942306281 := by
  unfold tailWord_1755140
  simp only [CollatzResearch.WordTrace]
  refine ⟨32007607430717504446235437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42676809907623339261647249 32007607430717504446235437)
  ·
    refine ⟨12002852786519064167338289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32007607430717504446235437 12002852786519064167338289)
    ·
      refine ⟨9002139589889298125503717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12002852786519064167338289 9002139589889298125503717)
      ·
        refine ⟨1687901173104243398531947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9002139589889298125503717 1687901173104243398531947)
        ·
          refine ⟨2531851759656365097797921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687901173104243398531947 2531851759656365097797921)
          ·
            refine ⟨1898888819742273823348441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531851759656365097797921 1898888819742273823348441)
            ·
              refine ⟨1424166614806705367511331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898888819742273823348441 1424166614806705367511331)
              ·
                refine ⟨2136249922210058051266997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424166614806705367511331 2136249922210058051266997)
                ·
                  refine ⟨200273430207192942306281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2136249922210058051266997 200273430207192942306281)
                  ·
                    rfl

theorem cell22_1755140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_1755140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755140 prefixEnd_1755140 := by exact prefixLift 1755140
  have htrace : WordTrace (prefixWord ++ tailWord_1755140) baseStart_1755140 baseEnd_1755140 := by
    simpa [prefixWord, tailWord_1755140, baseEnd_1755140] using wordTrace_append hprefix tailTrace_1755140
  have hstable : (prefixWord ++ tailWord_1755140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755140).length < 2 ^ (prefixWord ++ tailWord_1755140).sum := by decide
  have hdescent : baseEnd_1755140 < baseStart_1755140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755177 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_1755177 : Nat := 118140960795 + 1755177 * 2 ^ 59
def prefixEnd_1755177 : Nat := 4983230072969 + 3 ^ 40 * 1755177 * 2
def baseEnd_1755177 : Nat := 600832956477723063743729

theorem tailTrace_1755177 : CollatzResearch.WordTrace tailWord_1755177 prefixEnd_1755177 600832956477723063743729 := by
  unfold tailWord_1755177
  simp only [CollatzResearch.WordTrace]
  refine ⟨64016564362300964211567785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42677709574867309474378523 64016564362300964211567785)
  ·
    refine ⟨48012423271725723158675839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64016564362300964211567785 48012423271725723158675839)
    ·
      refine ⟨72018634907588584738013759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48012423271725723158675839 72018634907588584738013759)
      ·
        refine ⟨108027952361382877107020639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72018634907588584738013759 108027952361382877107020639)
        ·
          refine ⟨162041928542074315660530959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108027952361382877107020639 162041928542074315660530959)
          ·
            refine ⟨243062892813111473490796439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162041928542074315660530959 243062892813111473490796439)
            ·
              refine ⟨364594339219667210236194659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243062892813111473490796439 364594339219667210236194659)
              ·
                refine ⟨546891508829500815354291989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364594339219667210236194659 546891508829500815354291989)
                ·
                  refine ⟨25635539476382850719732437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 546891508829500815354291989 25635539476382850719732437)
                  ·
                    refine ⟨600832956477723063743729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25635539476382850719732437 600832956477723063743729)
                    ·
                      rfl

theorem cell22_1755177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_1755177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755177 prefixEnd_1755177 := by exact prefixLift 1755177
  have htrace : WordTrace (prefixWord ++ tailWord_1755177) baseStart_1755177 baseEnd_1755177 := by
    simpa [prefixWord, tailWord_1755177, baseEnd_1755177] using wordTrace_append hprefix tailTrace_1755177
  have hstable : (prefixWord ++ tailWord_1755177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755177).length < 2 ^ (prefixWord ++ tailWord_1755177).sum := by decide
  have hdescent : baseEnd_1755177 < baseStart_1755177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755239 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1755239 : Nat := 118140960795 + 1755239 * 2 ^ 59
def prefixEnd_1755239 : Nat := 4983230072969 + 3 ^ 40 * 1755239 * 2
def baseEnd_1755239 : Nat := 600854180344775568693539

theorem tailTrace_1755239 : CollatzResearch.WordTrace tailWord_1755239 prefixEnd_1755239 600854180344775568693539 := by
  unfold tailWord_1755239
  simp only [CollatzResearch.WordTrace]
  refine ⟨64018825688076348800324771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42679217125384232533549847 64018825688076348800324771)
  ·
    refine ⟨96028238532114523200487157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64018825688076348800324771 96028238532114523200487157)
    ·
      refine ⟨9002647362385736550045671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96028238532114523200487157 9002647362385736550045671)
      ·
        refine ⟨13503971043578604825068507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002647362385736550045671 13503971043578604825068507)
        ·
          refine ⟨20255956565367907237602761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13503971043578604825068507 20255956565367907237602761)
          ·
            refine ⟨15191967424025930428202071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20255956565367907237602761 15191967424025930428202071)
            ·
              refine ⟨22787951136038895642303107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15191967424025930428202071 22787951136038895642303107)
              ·
                refine ⟨34181926704058343463454661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22787951136038895642303107 34181926704058343463454661)
                ·
                  refine ⟨6409111257010939399397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34181926704058343463454661 6409111257010939399397749)
                  ·
                    refine ⟨600854180344775568693539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6409111257010939399397749 600854180344775568693539)
                    ·
                      rfl

theorem cell22_1755239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1755239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755239 prefixEnd_1755239 := by exact prefixLift 1755239
  have htrace : WordTrace (prefixWord ++ tailWord_1755239) baseStart_1755239 baseEnd_1755239 := by
    simpa [prefixWord, tailWord_1755239, baseEnd_1755239] using wordTrace_append hprefix tailTrace_1755239
  have hstable : (prefixWord ++ tailWord_1755239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755239).length < 2 ^ (prefixWord ++ tailWord_1755239).sum := by decide
  have hdescent : baseEnd_1755239 < baseStart_1755239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755271 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1755271 : Nat := 118140960795 + 1755271 * 2 ^ 59
def prefixEnd_1755271 : Nat := 4983230072969 + 3 ^ 40 * 1755271 * 2
def baseEnd_1755271 : Nat := 600865134598738151893441

theorem tailTrace_1755271 : CollatzResearch.WordTrace tailWord_1755271 prefixEnd_1755271 600865134598738151893441 := by
  unfold tailWord_1755271
  simp only [CollatzResearch.WordTrace]
  refine ⟨64019992823960418265489667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42679995215973612176993111 64019992823960418265489667)
  ·
    refine ⟨96029989235940627398234501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64019992823960418265489667 96029989235940627398234501)
    ·
      refine ⟨18005622981738867637168969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96029989235940627398234501 18005622981738867637168969)
      ·
        refine ⟨13504217236304150727876727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18005622981738867637168969 13504217236304150727876727)
        ·
          refine ⟨20256325854456226091815091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504217236304150727876727 20256325854456226091815091)
          ·
            refine ⟨30384488781684339137722637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256325854456226091815091 30384488781684339137722637)
            ·
              refine ⟨11394183293131627176645989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30384488781684339137722637 11394183293131627176645989)
              ·
                refine ⟨2136409367462180095621123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11394183293131627176645989 2136409367462180095621123)
                ·
                  refine ⟨3204614051193270143431685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136409367462180095621123 3204614051193270143431685)
                  ·
                    refine ⟨600865134598738151893441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204614051193270143431685 600865134598738151893441)
                    ·
                      rfl

theorem cell22_1755271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1755271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755271 prefixEnd_1755271 := by exact prefixLift 1755271
  have htrace : WordTrace (prefixWord ++ tailWord_1755271) baseStart_1755271 baseEnd_1755271 := by
    simpa [prefixWord, tailWord_1755271, baseEnd_1755271] using wordTrace_append hprefix tailTrace_1755271
  have hstable : (prefixWord ++ tailWord_1755271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755271).length < 2 ^ (prefixWord ++ tailWord_1755271).sum := by decide
  have hdescent : baseEnd_1755271 < baseStart_1755271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755301 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_1755301 : Nat := 118140960795 + 1755301 * 2 ^ 59
def prefixEnd_1755301 : Nat := 4983230072969 + 3 ^ 40 * 1755301 * 2
def baseEnd_1755301 : Nat := 600875404211828073643349

theorem tailTrace_1755301 : CollatzResearch.WordTrace tailWord_1755301 prefixEnd_1755301 600875404211828073643349 := by
  unfold tailWord_1755301
  simp only [CollatzResearch.WordTrace]
  refine ⟨64021087013851733389081757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42680724675901155592721171 64021087013851733389081757)
  ·
    refine ⟨24007907630194400020905659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64021087013851733389081757 24007907630194400020905659)
    ·
      refine ⟨36011861445291600031358489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24007907630194400020905659 36011861445291600031358489)
      ·
        refine ⟨27008896083968700023518867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36011861445291600031358489 27008896083968700023518867)
        ·
          refine ⟨40513344125953050035278301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27008896083968700023518867 40513344125953050035278301)
          ·
            refine ⟨15192504047232393763229363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40513344125953050035278301 15192504047232393763229363)
            ·
              refine ⟨22788756070848590644844045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15192504047232393763229363 22788756070848590644844045)
              ·
                refine ⟨8545783526568221491816517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22788756070848590644844045 8545783526568221491816517)
                ·
                  refine ⟨1602334411231541529715597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8545783526568221491816517 1602334411231541529715597)
                  ·
                    refine ⟨600875404211828073643349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1602334411231541529715597 600875404211828073643349)
                    ·
                      rfl

theorem cell22_1755301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_1755301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755301 prefixEnd_1755301 := by exact prefixLift 1755301
  have htrace : WordTrace (prefixWord ++ tailWord_1755301) baseStart_1755301 baseEnd_1755301 := by
    simpa [prefixWord, tailWord_1755301, baseEnd_1755301] using wordTrace_append hprefix tailTrace_1755301
  have hstable : (prefixWord ++ tailWord_1755301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755301).length < 2 ^ (prefixWord ++ tailWord_1755301).sum := by decide
  have hdescent : baseEnd_1755301 < baseStart_1755301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755344 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_1755344 : Nat := 118140960795 + 1755344 * 2 ^ 59
def prefixEnd_1755344 : Nat := 4983230072969 + 3 ^ 40 * 1755344 * 2
def baseEnd_1755344 : Nat := 600890123990590294818217

theorem tailTrace_1755344 : CollatzResearch.WordTrace tailWord_1755344 prefixEnd_1755344 600890123990590294818217 := by
  unfold tailWord_1755344
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011327676347975866448543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42681770235130634488598057 32011327676347975866448543)
  ·
    refine ⟨48016991514521963799672815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011327676347975866448543 48016991514521963799672815)
    ·
      refine ⟨72025487271782945699509223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48016991514521963799672815 72025487271782945699509223)
      ·
        refine ⟨108038230907674418549263835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72025487271782945699509223 108038230907674418549263835)
        ·
          refine ⟨162057346361511627823895753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108038230907674418549263835 162057346361511627823895753)
          ·
            refine ⟨121543009771133720867921815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162057346361511627823895753 121543009771133720867921815)
            ·
              refine ⟨182314514656700581301882723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121543009771133720867921815 182314514656700581301882723)
              ·
                refine ⟨273471771985050871952824085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182314514656700581301882723 273471771985050871952824085)
                ·
                  refine ⟨12818989311799259622788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 273471771985050871952824085 12818989311799259622788629)
                  ·
                    refine ⟨600890123990590294818217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12818989311799259622788629 600890123990590294818217)
                    ·
                      rfl

theorem cell22_1755344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_1755344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755344 prefixEnd_1755344 := by exact prefixLift 1755344
  have htrace : WordTrace (prefixWord ++ tailWord_1755344) baseStart_1755344 baseEnd_1755344 := by
    simpa [prefixWord, tailWord_1755344, baseEnd_1755344] using wordTrace_append hprefix tailTrace_1755344
  have hstable : (prefixWord ++ tailWord_1755344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755344).length < 2 ^ (prefixWord ++ tailWord_1755344).sum := by decide
  have hdescent : baseEnd_1755344 < baseStart_1755344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755350 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1755350 : Nat := 118140960795 + 1755350 * 2 ^ 59
def prefixEnd_1755350 : Nat := 4983230072969 + 3 ^ 40 * 1755350 * 2
def baseEnd_1755350 : Nat := 600892177913208279168199

theorem tailTrace_1755350 : CollatzResearch.WordTrace tailWord_1755350 prefixEnd_1755350 600892177913208279168199 := by
  unfold tailWord_1755350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001429636917138422350969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42681916127116143171743669 4001429636917138422350969)
  ·
    refine ⟨3001072227687853816763227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4001429636917138422350969 3001072227687853816763227)
    ·
      refine ⟨4501608341531780725144841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001072227687853816763227 4501608341531780725144841)
      ·
        refine ⟨3376206256148835543858631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4501608341531780725144841 3376206256148835543858631)
        ·
          refine ⟨5064309384223253315787947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376206256148835543858631 5064309384223253315787947)
          ·
            refine ⟨7596464076334879973681921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064309384223253315787947 7596464076334879973681921)
            ·
              refine ⟨5697348057251159980261441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596464076334879973681921 5697348057251159980261441)
              ·
                refine ⟨4273011042938369985196081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5697348057251159980261441 4273011042938369985196081)
                ·
                  refine ⟨3204758282203777488897061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273011042938369985196081 3204758282203777488897061)
                  ·
                    refine ⟨600892177913208279168199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204758282203777488897061 600892177913208279168199)
                    ·
                      rfl

theorem cell22_1755350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1755350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755350 prefixEnd_1755350 := by exact prefixLift 1755350
  have htrace : WordTrace (prefixWord ++ tailWord_1755350) baseStart_1755350 baseEnd_1755350 := by
    simpa [prefixWord, tailWord_1755350, baseEnd_1755350] using wordTrace_append hprefix tailTrace_1755350
  have hstable : (prefixWord ++ tailWord_1755350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755350).length < 2 ^ (prefixWord ++ tailWord_1755350).sum := by decide
  have hdescent : baseEnd_1755350 < baseStart_1755350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755468 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1755468 : Nat := 118140960795 + 1755468 * 2 ^ 59
def prefixEnd_1755468 : Nat := 4983230072969 + 3 ^ 40 * 1755468 * 2
def baseEnd_1755468 : Nat := 600932571724695304717837

theorem tailTrace_1755468 : CollatzResearch.WordTrace tailWord_1755468 prefixEnd_1755468 600932571724695304717837 := by
  unfold tailWord_1755468
  simp only [CollatzResearch.WordTrace]
  refine ⟨32013589002123360455205529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42684785336164480606940705 32013589002123360455205529)
  ·
    refine ⟨24010191751592520341404147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32013589002123360455205529 24010191751592520341404147)
    ·
      refine ⟨36015287627388780512106221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24010191751592520341404147 36015287627388780512106221)
      ·
        refine ⟨13505732860270792692039833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36015287627388780512106221 13505732860270792692039833)
        ·
          refine ⟨10129299645203094519029875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13505732860270792692039833 10129299645203094519029875)
          ·
            refine ⟨15193949467804641778544813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10129299645203094519029875 15193949467804641778544813)
            ·
              refine ⟨5697731050426740666954305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15193949467804641778544813 5697731050426740666954305)
              ·
                refine ⟨4273298287820055500215729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5697731050426740666954305 4273298287820055500215729)
                ·
                  refine ⟨3204973715865041625161797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4273298287820055500215729 3204973715865041625161797)
                  ·
                    refine ⟨600932571724695304717837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3204973715865041625161797 600932571724695304717837)
                    ·
                      rfl

theorem cell22_1755468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1755468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755468 prefixEnd_1755468 := by exact prefixLift 1755468
  have htrace : WordTrace (prefixWord ++ tailWord_1755468) baseStart_1755468 baseEnd_1755468 := by
    simpa [prefixWord, tailWord_1755468, baseEnd_1755468] using wordTrace_append hprefix tailTrace_1755468
  have hstable : (prefixWord ++ tailWord_1755468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755468).length < 2 ^ (prefixWord ++ tailWord_1755468).sum := by decide
  have hdescent : baseEnd_1755468 < baseStart_1755468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755511 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 7]
def baseStart_1755511 : Nat := 118140960795 + 1755511 * 2 ^ 59
def prefixEnd_1755511 : Nat := 4983230072969 + 3 ^ 40 * 1755511 * 2
def baseEnd_1755511 : Nat := 200315763834485841964235

theorem tailTrace_1755511 : CollatzResearch.WordTrace tailWord_1755511 prefixEnd_1755511 200315763834485841964235 := by
  unfold tailWord_1755511
  simp only [CollatzResearch.WordTrace]
  refine ⟨64028746343090939254226387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42685830895393959502817591 64028746343090939254226387)
  ·
    refine ⟨96043119514636408881339581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64028746343090939254226387 96043119514636408881339581)
    ·
      refine ⟨36016169817988653330502343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96043119514636408881339581 36016169817988653330502343)
      ·
        refine ⟨54024254726982979995753515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36016169817988653330502343 54024254726982979995753515)
        ·
          refine ⟨81036382090474469993630273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54024254726982979995753515 81036382090474469993630273)
          ·
            refine ⟨60777286567855852495222705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81036382090474469993630273 60777286567855852495222705)
            ·
              refine ⟨45582964925891889371417029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60777286567855852495222705 45582964925891889371417029)
              ·
                refine ⟨8546805923604729257140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45582964925891889371417029 8546805923604729257140693)
                ·
                  refine ⟨200315763834485841964235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8546805923604729257140693 200315763834485841964235)
                  ·
                    rfl

theorem cell22_1755511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_1755511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755511 prefixEnd_1755511 := by exact prefixLift 1755511
  have htrace : WordTrace (prefixWord ++ tailWord_1755511) baseStart_1755511 baseEnd_1755511 := by
    simpa [prefixWord, tailWord_1755511, baseEnd_1755511] using wordTrace_append hprefix tailTrace_1755511
  have hstable : (prefixWord ++ tailWord_1755511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755511).length < 2 ^ (prefixWord ++ tailWord_1755511).sum := by decide
  have hdescent : baseEnd_1755511 < baseStart_1755511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755532 : List Nat := [2, 2, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_1755532 : Nat := 118140960795 + 1755532 * 2 ^ 59
def prefixEnd_1755532 : Nat := 4983230072969 + 3 ^ 40 * 1755532 * 2
def baseEnd_1755532 : Nat := 600954480232620471117641

theorem tailTrace_1755532 : CollatzResearch.WordTrace tailWord_1755532 prefixEnd_1755532 600954480232620471117641 := by
  unfold tailWord_1755532
  simp only [CollatzResearch.WordTrace]
  refine ⟨32014756138007429920370425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42686341517343239893827233 32014756138007429920370425)
  ·
    refine ⟨24011067103505572440277819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32014756138007429920370425 24011067103505572440277819)
    ·
      refine ⟨36016600655258358660416729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24011067103505572440277819 36016600655258358660416729)
      ·
        refine ⟨27012450491443768995312547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36016600655258358660416729 27012450491443768995312547)
        ·
          refine ⟨40518675737165653492968821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27012450491443768995312547 40518675737165653492968821)
          ·
            refine ⟨3798625850359280014965827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40518675737165653492968821 3798625850359280014965827)
            ·
              refine ⟨5697938775538920022448741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798625850359280014965827 5697938775538920022448741)
              ·
                refine ⟨1068363520413547504209139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5697938775538920022448741 1068363520413547504209139)
                ·
                  refine ⟨1602545280620321256313709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068363520413547504209139 1602545280620321256313709)
                  ·
                    refine ⟨600954480232620471117641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1602545280620321256313709 600954480232620471117641)
                    ·
                      rfl

theorem cell22_1755532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_1755532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755532 prefixEnd_1755532 := by exact prefixLift 1755532
  have htrace : WordTrace (prefixWord ++ tailWord_1755532) baseStart_1755532 baseEnd_1755532 := by
    simpa [prefixWord, tailWord_1755532, baseEnd_1755532] using wordTrace_append hprefix tailTrace_1755532
  have hstable : (prefixWord ++ tailWord_1755532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755532).length < 2 ^ (prefixWord ++ tailWord_1755532).sum := by decide
  have hdescent : baseEnd_1755532 < baseStart_1755532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755575 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1755575 : Nat := 118140960795 + 1755575 * 2 ^ 59
def prefixEnd_1755575 : Nat := 4983230072969 + 3 ^ 40 * 1755575 * 2
def baseEnd_1755575 : Nat := 600969200011382692292509

theorem tailTrace_1755575 : CollatzResearch.WordTrace tailWord_1755575 prefixEnd_1755575 600969200011382692292509 := by
  unfold tailWord_1755575
  simp only [CollatzResearch.WordTrace]
  refine ⟨64031080614859078184556179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42687387076572718789704119 64031080614859078184556179)
  ·
    refine ⟨96046620922288617276834269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64031080614859078184556179 96046620922288617276834269)
    ·
      refine ⟨36017482845858231478812851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96046620922288617276834269 36017482845858231478812851)
      ·
        refine ⟨54026224268787347218219277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36017482845858231478812851 54026224268787347218219277)
        ·
          refine ⟨20259834100795255206832229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54026224268787347218219277 20259834100795255206832229)
          ·
            refine ⟨3798718893899110351281043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20259834100795255206832229 3798718893899110351281043)
            ·
              refine ⟨5698078340848665526921565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798718893899110351281043 5698078340848665526921565)
              ·
                refine ⟨2136779377818249572595587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5698078340848665526921565 2136779377818249572595587)
                ·
                  refine ⟨3205169066727374358893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136779377818249572595587 3205169066727374358893381)
                  ·
                    refine ⟨600969200011382692292509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3205169066727374358893381 600969200011382692292509)
                    ·
                      rfl

theorem cell22_1755575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1755575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755575 prefixEnd_1755575 := by exact prefixLift 1755575
  have htrace : WordTrace (prefixWord ++ tailWord_1755575) baseStart_1755575 baseEnd_1755575 := by
    simpa [prefixWord, tailWord_1755575, baseEnd_1755575] using wordTrace_append hprefix tailTrace_1755575
  have hstable : (prefixWord ++ tailWord_1755575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755575).length < 2 ^ (prefixWord ++ tailWord_1755575).sum := by decide
  have hdescent : baseEnd_1755575 < baseStart_1755575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755605 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1755605 : Nat := 118140960795 + 1755605 * 2 ^ 59
def prefixEnd_1755605 : Nat := 4983230072969 + 3 ^ 40 * 1755605 * 2
def baseEnd_1755605 : Nat := 600979469624472614042417

theorem tailTrace_1755605 : CollatzResearch.WordTrace tailWord_1755605 prefixEnd_1755605 600979469624472614042417 := by
  unfold tailWord_1755605
  simp only [CollatzResearch.WordTrace]
  refine ⟨64032174804750393308148269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42688116536500262205432179 64032174804750393308148269)
  ·
    refine ⟨24012065551781397490555601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64032174804750393308148269 24012065551781397490555601)
    ·
      refine ⟨18009049163836048117916701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24012065551781397490555601 18009049163836048117916701)
      ·
        refine ⟨6753393436438518044218763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18009049163836048117916701 6753393436438518044218763)
        ·
          refine ⟨10130090154657777066328145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753393436438518044218763 10130090154657777066328145)
          ·
            refine ⟨7597567615993332799746109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10130090154657777066328145 7597567615993332799746109)
            ·
              refine ⟨2849087855997499799904791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7597567615993332799746109 2849087855997499799904791)
              ·
                refine ⟨4273631783996249699857187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849087855997499799904791 4273631783996249699857187)
                ·
                  refine ⟨6410447675994374549785781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273631783996249699857187 6410447675994374549785781)
                  ·
                    refine ⟨600979469624472614042417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6410447675994374549785781 600979469624472614042417)
                    ·
                      rfl

theorem cell22_1755605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1755605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755605 prefixEnd_1755605 := by exact prefixLift 1755605
  have htrace : WordTrace (prefixWord ++ tailWord_1755605) baseStart_1755605 baseEnd_1755605 := by
    simpa [prefixWord, tailWord_1755605, baseEnd_1755605] using wordTrace_append hprefix tailTrace_1755605
  have hstable : (prefixWord ++ tailWord_1755605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755605).length < 2 ^ (prefixWord ++ tailWord_1755605).sum := by decide
  have hdescent : baseEnd_1755605 < baseStart_1755605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755825 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_1755825 : Nat := 118140960795 + 1755825 * 2 ^ 59
def prefixEnd_1755825 : Nat := 4983230072969 + 3 ^ 40 * 1755825 * 2
def baseEnd_1755825 : Nat := 601054780120465373541743

theorem tailTrace_1755825 : CollatzResearch.WordTrace tailWord_1755825 prefixEnd_1755825 601054780120465373541743 := by
  unfold tailWord_1755825
  simp only [CollatzResearch.WordTrace]
  refine ⟨64040198863953370881156929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42693465909302247254104619 64040198863953370881156929)
  ·
    refine ⟨48030149147965028160867697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64040198863953370881156929 48030149147965028160867697)
    ·
      refine ⟨36022611860973771120650773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48030149147965028160867697 36022611860973771120650773)
      ·
        refine ⟨1688559930983145521280505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36022611860973771120650773 1688559930983145521280505)
        ·
          refine ⟨1266419948237359140960379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688559930983145521280505 1266419948237359140960379)
          ·
            refine ⟨1899629922356038711440569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266419948237359140960379 1899629922356038711440569)
            ·
              refine ⟨1424722441767029033580427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899629922356038711440569 1424722441767029033580427)
              ·
                refine ⟨2137083662650543550370641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424722441767029033580427 2137083662650543550370641)
                ·
                  refine ⟨1602812746987907662777981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137083662650543550370641 1602812746987907662777981)
                  ·
                    refine ⟨601054780120465373541743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1602812746987907662777981 601054780120465373541743)
                    ·
                      rfl

theorem cell22_1755825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_1755825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755825 prefixEnd_1755825 := by exact prefixLift 1755825
  have htrace : WordTrace (prefixWord ++ tailWord_1755825) baseStart_1755825 baseEnd_1755825 := by
    simpa [prefixWord, tailWord_1755825, baseEnd_1755825] using wordTrace_append hprefix tailTrace_1755825
  have hstable : (prefixWord ++ tailWord_1755825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755825).length < 2 ^ (prefixWord ++ tailWord_1755825).sum := by decide
  have hdescent : baseEnd_1755825 < baseStart_1755825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755911 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 4]
def baseStart_1755911 : Nat := 118140960795 + 1755911 * 2 ^ 59
def prefixEnd_1755911 : Nat := 4983230072969 + 3 ^ 40 * 1755911 * 2
def baseEnd_1755911 : Nat := 200361406559329938630493

theorem tailTrace_1755911 : CollatzResearch.WordTrace tailWord_1755911 prefixEnd_1755911 200361406559329938630493 := by
  unfold tailWord_1755911
  simp only [CollatzResearch.WordTrace]
  refine ⟨64043335541641807568787587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42695557027761205045858391 64043335541641807568787587)
  ·
    refine ⟨96065003312462711353181381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64043335541641807568787587 96065003312462711353181381)
    ·
      refine ⟨18012188121086758378721509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96065003312462711353181381 18012188121086758378721509)
      ·
        refine ⟨3377285272703767196010283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18012188121086758378721509 3377285272703767196010283)
        ·
          refine ⟨5065927909055650794015425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377285272703767196010283 5065927909055650794015425)
          ·
            refine ⟨3799445931791738095511569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065927909055650794015425 3799445931791738095511569)
            ·
              refine ⟨2849584448843803571633677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799445931791738095511569 2849584448843803571633677)
              ·
                refine ⟨1068594168316426339362629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2849584448843803571633677 1068594168316426339362629)
                ·
                  refine ⟨200361406559329938630493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068594168316426339362629 200361406559329938630493)
                  ·
                    rfl

theorem cell22_1755911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 4].length) (baseStart_1755911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755911 prefixEnd_1755911 := by exact prefixLift 1755911
  have htrace : WordTrace (prefixWord ++ tailWord_1755911) baseStart_1755911 baseEnd_1755911 := by
    simpa [prefixWord, tailWord_1755911, baseEnd_1755911] using wordTrace_append hprefix tailTrace_1755911
  have hstable : (prefixWord ++ tailWord_1755911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755911).length < 2 ^ (prefixWord ++ tailWord_1755911).sum := by decide
  have hdescent : baseEnd_1755911 < baseStart_1755911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755954 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1755954 : Nat := 118140960795 + 1755954 * 2 ^ 59
def prefixEnd_1755954 : Nat := 4983230072969 + 3 ^ 40 * 1755954 * 2
def baseEnd_1755954 : Nat := 601098939456752037066347

theorem tailTrace_1755954 : CollatzResearch.WordTrace tailWord_1755954 prefixEnd_1755954 601098939456752037066347 := by
  unfold tailWord_1755954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16011225970121506478150729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42696602586990683941735277 16011225970121506478150729)
  ·
    refine ⟨12008419477591129858613047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16011225970121506478150729 12008419477591129858613047)
    ·
      refine ⟨18012629216386694787919571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12008419477591129858613047 18012629216386694787919571)
      ·
        refine ⟨27018943824580042181879357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18012629216386694787919571 27018943824580042181879357)
        ·
          refine ⟨10132103934217515818204759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27018943824580042181879357 10132103934217515818204759)
          ·
            refine ⟨15198155901326273727307139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132103934217515818204759 15198155901326273727307139)
            ·
              refine ⟨22797233851989410590960709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15198155901326273727307139 22797233851989410590960709)
              ·
                refine ⟨4274481347248014485805133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22797233851989410590960709 4274481347248014485805133)
                ·
                  refine ⟨1602930505218005432176925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4274481347248014485805133 1602930505218005432176925)
                  ·
                    refine ⟨601098939456752037066347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1602930505218005432176925 601098939456752037066347)
                    ·
                      rfl

theorem cell22_1755954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1755954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755954 prefixEnd_1755954 := by exact prefixLift 1755954
  have htrace : WordTrace (prefixWord ++ tailWord_1755954) baseStart_1755954 baseEnd_1755954 := by
    simpa [prefixWord, tailWord_1755954, baseEnd_1755954] using wordTrace_append hprefix tailTrace_1755954
  have hstable : (prefixWord ++ tailWord_1755954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755954).length < 2 ^ (prefixWord ++ tailWord_1755954).sum := by decide
  have hdescent : baseEnd_1755954 < baseStart_1755954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755967 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 7]
def baseStart_1755967 : Nat := 118140960795 + 1755967 * 2 ^ 59
def prefixEnd_1755967 : Nat := 4983230072969 + 3 ^ 40 * 1755967 * 2
def baseEnd_1755967 : Nat := 200367796540808112163769

theorem tailTrace_1755967 : CollatzResearch.WordTrace tailWord_1755967 prefixEnd_1755967 200367796540808112163769 := by
  unfold tailWord_1755967
  simp only [CollatzResearch.WordTrace]
  refine ⟨64045378029438929132826155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42696918686292619421884103 64045378029438929132826155)
  ·
    refine ⟨96068067044158393699239233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64045378029438929132826155 96068067044158393699239233)
    ·
      refine ⟨72051050283118795274429425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96068067044158393699239233 72051050283118795274429425)
      ·
        refine ⟨54038287712339096455822069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72051050283118795274429425 54038287712339096455822069)
        ·
          refine ⟨5066089473031790292733319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54038287712339096455822069 5066089473031790292733319)
          ·
            refine ⟨7599134209547685439099979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066089473031790292733319 7599134209547685439099979)
            ·
              refine ⟨11398701314321528158649969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599134209547685439099979 11398701314321528158649969)
              ·
                refine ⟨8549025985741146118987477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11398701314321528158649969 8549025985741146118987477)
                ·
                  refine ⟨200367796540808112163769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8549025985741146118987477 200367796540808112163769)
                  ·
                    rfl

theorem cell22_1755967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_1755967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755967 prefixEnd_1755967 := by exact prefixLift 1755967
  have htrace : WordTrace (prefixWord ++ tailWord_1755967) baseStart_1755967 baseEnd_1755967 := by
    simpa [prefixWord, tailWord_1755967, baseEnd_1755967] using wordTrace_append hprefix tailTrace_1755967
  have hstable : (prefixWord ++ tailWord_1755967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755967).length < 2 ^ (prefixWord ++ tailWord_1755967).sum := by decide
  have hdescent : baseEnd_1755967 < baseStart_1755967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755982 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1755982 : Nat := 118140960795 + 1755982 * 2 ^ 59
def prefixEnd_1755982 : Nat := 4983230072969 + 3 ^ 40 * 1755982 * 2
def baseEnd_1755982 : Nat := 601108524428969297366261

theorem tailTrace_1755982 : CollatzResearch.WordTrace tailWord_1755982 prefixEnd_1755982 601108524428969297366261 := by
  unfold tailWord_1755982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005740640548073336827775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42697283416256391129748133 8005740640548073336827775)
  ·
    refine ⟨12008610960822110005241663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8005740640548073336827775 12008610960822110005241663)
    ·
      refine ⟨18012916441233165007862495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12008610960822110005241663 18012916441233165007862495)
      ·
        refine ⟨27019374661849747511793743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18012916441233165007862495 27019374661849747511793743)
        ·
          refine ⟨40529061992774621267690615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27019374661849747511793743 40529061992774621267690615)
          ·
            refine ⟨60793592989161931901535923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40529061992774621267690615 60793592989161931901535923)
            ·
              refine ⟨91190389483742897852303885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60793592989161931901535923 91190389483742897852303885)
              ·
                refine ⟨34196396056403586694613957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91190389483742897852303885 34196396056403586694613957)
                ·
                  refine ⟨6411824260575672505240117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34196396056403586694613957 6411824260575672505240117)
                  ·
                    refine ⟨601108524428969297366261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6411824260575672505240117 601108524428969297366261)
                    ·
                      rfl

theorem cell22_1755982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1755982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755982 prefixEnd_1755982 := by exact prefixLift 1755982
  have htrace : WordTrace (prefixWord ++ tailWord_1755982) baseStart_1755982 baseEnd_1755982 := by
    simpa [prefixWord, tailWord_1755982, baseEnd_1755982] using wordTrace_append hprefix tailTrace_1755982
  have hstable : (prefixWord ++ tailWord_1755982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755982).length < 2 ^ (prefixWord ++ tailWord_1755982).sum := by decide
  have hdescent : baseEnd_1755982 < baseStart_1755982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755988 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1755988 : Nat := 118140960795 + 1755988 * 2 ^ 59
def prefixEnd_1755988 : Nat := 4983230072969 + 3 ^ 40 * 1755988 * 2
def baseEnd_1755988 : Nat := 601110578351587281716243

theorem tailTrace_1755988 : CollatzResearch.WordTrace tailWord_1755988 prefixEnd_1755988 601110578351587281716243 := by
  unfold tailWord_1755988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023071981181424859670309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42697429308241899812893745 32023071981181424859670309)
  ·
    refine ⟨6004325996471517161188183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32023071981181424859670309 6004325996471517161188183)
    ·
      refine ⟨9006488994707275741782275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004325996471517161188183 9006488994707275741782275)
      ·
        refine ⟨13509733492060913612673413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9006488994707275741782275 13509733492060913612673413)
        ·
          refine ⟨2533075029761421302376265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13509733492060913612673413 2533075029761421302376265)
          ·
            refine ⟨1899806272321065976782199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533075029761421302376265 1899806272321065976782199)
            ·
              refine ⟨2849709408481598965173299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899806272321065976782199 2849709408481598965173299)
              ·
                refine ⟨4274564112722398447759949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849709408481598965173299 4274564112722398447759949)
                ·
                  refine ⟨1602961542270899417909981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4274564112722398447759949 1602961542270899417909981)
                  ·
                    refine ⟨601110578351587281716243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1602961542270899417909981 601110578351587281716243)
                    ·
                      rfl

theorem cell22_1755988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1755988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1755988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1755988 prefixEnd_1755988 := by exact prefixLift 1755988
  have htrace : WordTrace (prefixWord ++ tailWord_1755988) baseStart_1755988 baseEnd_1755988 := by
    simpa [prefixWord, tailWord_1755988, baseEnd_1755988] using wordTrace_append hprefix tailTrace_1755988
  have hstable : (prefixWord ++ tailWord_1755988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755988).length < 2 ^ (prefixWord ++ tailWord_1755988).sum := by decide
  have hdescent : baseEnd_1755988 < baseStart_1755988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756012 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_1756012 : Nat := 118140960795 + 1756012 * 2 ^ 59
def prefixEnd_1756012 : Nat := 4983230072969 + 3 ^ 40 * 1756012 * 2
def baseEnd_1756012 : Nat := 200372931347353073038723

theorem tailTrace_1756012 : CollatzResearch.WordTrace tailWord_1756012 prefixEnd_1756012 200372931347353073038723 := by
  unfold tailWord_1756012
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023509657137950909107145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42698012876183934545476193 32023509657137950909107145)
  ·
    refine ⟨24017632242853463181830359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32023509657137950909107145 24017632242853463181830359)
    ·
      refine ⟨36026448364280194772745539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24017632242853463181830359 36026448364280194772745539)
      ·
        refine ⟨54039672546420292159118309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36026448364280194772745539 54039672546420292159118309)
        ·
          refine ⟨10132438602453804779834683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54039672546420292159118309 10132438602453804779834683)
          ·
            refine ⟨15198657903680707169752025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132438602453804779834683 15198657903680707169752025)
            ·
              refine ⟨11398993427760530377314019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15198657903680707169752025 11398993427760530377314019)
              ·
                refine ⟨17098490141640795565971029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398993427760530377314019 17098490141640795565971029)
                ·
                  refine ⟨200372931347353073038723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17098490141640795565971029 200372931347353073038723)
                  ·
                    rfl

theorem cell22_1756012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_1756012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756012 prefixEnd_1756012 := by exact prefixLift 1756012
  have htrace : WordTrace (prefixWord ++ tailWord_1756012) baseStart_1756012 baseEnd_1756012 := by
    simpa [prefixWord, tailWord_1756012, baseEnd_1756012] using wordTrace_append hprefix tailTrace_1756012
  have hstable : (prefixWord ++ tailWord_1756012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756012).length < 2 ^ (prefixWord ++ tailWord_1756012).sum := by decide
  have hdescent : baseEnd_1756012 < baseStart_1756012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756027 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_1756027 : Nat := 118140960795 + 1756027 * 2 ^ 59
def prefixEnd_1756027 : Nat := 4983230072969 + 3 ^ 40 * 1756027 * 2
def baseEnd_1756027 : Nat := 601123928848604179991123

theorem tailTrace_1756027 : CollatzResearch.WordTrace tailWord_1756027 prefixEnd_1756027 601123928848604179991123 := by
  unfold tailWord_1756027
  simp only [CollatzResearch.WordTrace]
  refine ⟨64047566409221559380010335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42698377606147706253340223 64047566409221559380010335)
  ·
    refine ⟨96071349613832339070015503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64047566409221559380010335 96071349613832339070015503)
    ·
      refine ⟨144107024420748508605023255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96071349613832339070015503 144107024420748508605023255)
      ·
        refine ⟨216160536631122762907534883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144107024420748508605023255 216160536631122762907534883)
        ·
          refine ⟨324240804946684144361302325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216160536631122762907534883 324240804946684144361302325)
          ·
            refine ⟨30397575463751638533872093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324240804946684144361302325 30397575463751638533872093)
            ·
              refine ⟨11399090798906864450202035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30397575463751638533872093 11399090798906864450202035)
              ·
                refine ⟨17098636198360296675303053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399090798906864450202035 17098636198360296675303053)
                ·
                  refine ⟨6411988574385111253238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17098636198360296675303053 6411988574385111253238645)
                  ·
                    refine ⟨601123928848604179991123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6411988574385111253238645 601123928848604179991123)
                    ·
                      rfl

theorem cell22_1756027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_1756027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756027 prefixEnd_1756027 := by exact prefixLift 1756027
  have htrace : WordTrace (prefixWord ++ tailWord_1756027) baseStart_1756027 baseEnd_1756027 := by
    simpa [prefixWord, tailWord_1756027, baseEnd_1756027] using wordTrace_append hprefix tailTrace_1756027
  have hstable : (prefixWord ++ tailWord_1756027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756027).length < 2 ^ (prefixWord ++ tailWord_1756027).sum := by decide
  have hdescent : baseEnd_1756027 < baseStart_1756027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756044 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1756044 : Nat := 118140960795 + 1756044 * 2 ^ 59
def prefixEnd_1756044 : Nat := 4983230072969 + 3 ^ 40 * 1756044 * 2
def baseEnd_1756044 : Nat := 601129748296021802316071

theorem tailTrace_1756044 : CollatzResearch.WordTrace tailWord_1756044 prefixEnd_1756044 601129748296021802316071 := by
  unfold tailWord_1756044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32024093225079985641689593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42698790966773314188919457 32024093225079985641689593)
  ·
    refine ⟨24018069918809989231267195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32024093225079985641689593 24018069918809989231267195)
    ·
      refine ⟨36027104878214983846900793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24018069918809989231267195 36027104878214983846900793)
      ·
        refine ⟨27020328658661237885175595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36027104878214983846900793 27020328658661237885175595)
        ·
          refine ⟨40530492987991856827763393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27020328658661237885175595 40530492987991856827763393)
          ·
            refine ⟨30397869740993892620822545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40530492987991856827763393 30397869740993892620822545)
            ·
              refine ⟨22798402305745419465616909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30397869740993892620822545 22798402305745419465616909)
              ·
                refine ⟨8549400864654532299606341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22798402305745419465616909 8549400864654532299606341)
                ·
                  refine ⟨1603012662122724806176189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8549400864654532299606341 1603012662122724806176189)
                  ·
                    refine ⟨601129748296021802316071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603012662122724806176189 601129748296021802316071)
                    ·
                      rfl

theorem cell22_1756044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1756044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756044 prefixEnd_1756044 := by exact prefixLift 1756044
  have htrace : WordTrace (prefixWord ++ tailWord_1756044) baseStart_1756044 baseEnd_1756044 := by
    simpa [prefixWord, tailWord_1756044, baseEnd_1756044] using wordTrace_append hprefix tailTrace_1756044
  have hstable : (prefixWord ++ tailWord_1756044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756044).length < 2 ^ (prefixWord ++ tailWord_1756044).sum := by decide
  have hdescent : baseEnd_1756044 < baseStart_1756044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756061 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1756061 : Nat := 118140960795 + 1756061 * 2 ^ 59
def prefixEnd_1756061 : Nat := 4983230072969 + 3 ^ 40 * 1756061 * 2
def baseEnd_1756061 : Nat := 601135567743439424641019

theorem tailTrace_1756061 : CollatzResearch.WordTrace tailWord_1756061 prefixEnd_1756061 601135567743439424641019 := by
  unfold tailWord_1756061
  simp only [CollatzResearch.WordTrace]
  refine ⟨64048806491098383186748037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42699204327398922124498691 64048806491098383186748037)
  ·
    refine ⟨12009151217080946847515257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64048806491098383186748037 12009151217080946847515257)
    ·
      refine ⟨9006863412810710135636443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12009151217080946847515257 9006863412810710135636443)
      ·
        refine ⟨13510295119216065203454665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9006863412810710135636443 13510295119216065203454665)
        ·
          refine ⟨10132721339412048902590999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13510295119216065203454665 10132721339412048902590999)
          ·
            refine ⟨15199082009118073353886499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132721339412048902590999 15199082009118073353886499)
            ·
              refine ⟨22798623013677110030829749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15199082009118073353886499 22798623013677110030829749)
              ·
                refine ⟨2137370907532229065390289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22798623013677110030829749 2137370907532229065390289)
                ·
                  refine ⟨1603028180649171799042717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137370907532229065390289 1603028180649171799042717)
                  ·
                    refine ⟨601135567743439424641019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603028180649171799042717 601135567743439424641019)
                    ·
                      rfl

theorem cell22_1756061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1756061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756061 prefixEnd_1756061 := by exact prefixLift 1756061
  have htrace : WordTrace (prefixWord ++ tailWord_1756061) baseStart_1756061 baseEnd_1756061 := by
    simpa [prefixWord, tailWord_1756061, baseEnd_1756061] using wordTrace_append hprefix tailTrace_1756061
  have hstable : (prefixWord ++ tailWord_1756061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756061).length < 2 ^ (prefixWord ++ tailWord_1756061).sum := by decide
  have hdescent : baseEnd_1756061 < baseStart_1756061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756179 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_1756179 : Nat := 118140960795 + 1756179 * 2 ^ 59
def prefixEnd_1756179 : Nat := 4983230072969 + 3 ^ 40 * 1756179 * 2
def baseEnd_1756179 : Nat := 601175961554926450190657

theorem tailTrace_1756179 : CollatzResearch.WordTrace tailWord_1756179 prefixEnd_1756179 601175961554926450190657 := by
  unfold tailWord_1756179
  simp only [CollatzResearch.WordTrace]
  refine ⟨64053110304670889339543591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42702073536447259559695727 64053110304670889339543591)
  ·
    refine ⟨96079665457006334009315387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64053110304670889339543591 96079665457006334009315387)
    ·
      refine ⟨144119498185509501013973081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96079665457006334009315387 144119498185509501013973081)
      ·
        refine ⟨108089623639132125760479811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144119498185509501013973081 108089623639132125760479811)
        ·
          refine ⟨162134435458698188640719717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108089623639132125760479811 162134435458698188640719717)
          ·
            refine ⟨30400206648505910370134947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162134435458698188640719717 30400206648505910370134947)
            ·
              refine ⟨45600309972758865555202421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30400206648505910370134947 45600309972758865555202421)
              ·
                refine ⟨4275029059946143645800227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45600309972758865555202421 4275029059946143645800227)
                ·
                  refine ⟨6412543589919215468700341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275029059946143645800227 6412543589919215468700341)
                  ·
                    refine ⟨601175961554926450190657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6412543589919215468700341 601175961554926450190657)
                    ·
                      rfl

theorem cell22_1756179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_1756179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756179 prefixEnd_1756179 := by exact prefixLift 1756179
  have htrace : WordTrace (prefixWord ++ tailWord_1756179) baseStart_1756179 baseEnd_1756179 := by
    simpa [prefixWord, tailWord_1756179, baseEnd_1756179] using wordTrace_append hprefix tailTrace_1756179
  have hstable : (prefixWord ++ tailWord_1756179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756179).length < 2 ^ (prefixWord ++ tailWord_1756179).sum := by decide
  have hdescent : baseEnd_1756179 < baseStart_1756179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756183 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1756183 : Nat := 118140960795 + 1756183 * 2 ^ 59
def prefixEnd_1756183 : Nat := 4983230072969 + 3 ^ 40 * 1756183 * 2
def baseEnd_1756183 : Nat := 601177330836671773090645

theorem tailTrace_1756183 : CollatzResearch.WordTrace tailWord_1756183 prefixEnd_1756183 601177330836671773090645 := by
  unfold tailWord_1756183
  simp only [CollatzResearch.WordTrace]
  refine ⟨64053256196656398022689203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42702170797770932015126135 64053256196656398022689203)
  ·
    refine ⟨96079884294984597034033805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64053256196656398022689203 96079884294984597034033805)
    ·
      refine ⟨36029956610619223887762677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96079884294984597034033805 36029956610619223887762677)
      ·
        refine ⟨3377808432245552239477751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36029956610619223887762677 3377808432245552239477751)
        ·
          refine ⟨5066712648368328359216627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377808432245552239477751 5066712648368328359216627)
          ·
            refine ⟨7600068972552492538824941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066712648368328359216627 7600068972552492538824941)
            ·
              refine ⟨2850025864707184702059353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7600068972552492538824941 2850025864707184702059353)
              ·
                refine ⟨2137519398530388526544515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850025864707184702059353 2137519398530388526544515)
                ·
                  refine ⟨3206279097795582789816773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137519398530388526544515 3206279097795582789816773)
                  ·
                    refine ⟨601177330836671773090645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206279097795582789816773 601177330836671773090645)
                    ·
                      rfl

theorem cell22_1756183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1756183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756183 prefixEnd_1756183 := by exact prefixLift 1756183
  have htrace : WordTrace (prefixWord ++ tailWord_1756183) baseStart_1756183 baseEnd_1756183 := by
    simpa [prefixWord, tailWord_1756183, baseEnd_1756183] using wordTrace_append hprefix tailTrace_1756183
  have hstable : (prefixWord ++ tailWord_1756183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756183).length < 2 ^ (prefixWord ++ tailWord_1756183).sum := by decide
  have hdescent : baseEnd_1756183 < baseStart_1756183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756196 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1756196 : Nat := 118140960795 + 1756196 * 2 ^ 59
def prefixEnd_1756196 : Nat := 4983230072969 + 3 ^ 40 * 1756196 * 2
def baseEnd_1756196 : Nat := 601181781002344072515605

theorem tailTrace_1756196 : CollatzResearch.WordTrace tailWord_1756196 prefixEnd_1756196 601181781002344072515605 := by
  unfold tailWord_1756196
  simp only [CollatzResearch.WordTrace]
  refine ⟨32026865172804650621456221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42702486897072867495274961 32026865172804650621456221)
  ·
    refine ⟨12010074439801743983046083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32026865172804650621456221 12010074439801743983046083)
    ·
      refine ⟨18015111659702615974569125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010074439801743983046083 18015111659702615974569125)
      ·
        refine ⟨3377833436194240495231711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18015111659702615974569125 3377833436194240495231711)
        ·
          refine ⟨5066750154291360742847567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377833436194240495231711 5066750154291360742847567)
          ·
            refine ⟨7600125231437041114271351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066750154291360742847567 7600125231437041114271351)
            ·
              refine ⟨11400187847155561671407027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600125231437041114271351 11400187847155561671407027)
              ·
                refine ⟨17100281770733342507110541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11400187847155561671407027 17100281770733342507110541)
                ·
                  refine ⟨6412605664025003440166453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17100281770733342507110541 6412605664025003440166453)
                  ·
                    refine ⟨601181781002344072515605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6412605664025003440166453 601181781002344072515605)
                    ·
                      rfl

theorem cell22_1756196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1756196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756196 prefixEnd_1756196 := by exact prefixLift 1756196
  have htrace : WordTrace (prefixWord ++ tailWord_1756196) baseStart_1756196 baseEnd_1756196 := by
    simpa [prefixWord, tailWord_1756196, baseEnd_1756196] using wordTrace_append hprefix tailTrace_1756196
  have hstable : (prefixWord ++ tailWord_1756196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756196).length < 2 ^ (prefixWord ++ tailWord_1756196).sum := by decide
  have hdescent : baseEnd_1756196 < baseStart_1756196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756230 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1756230 : Nat := 118140960795 + 1756230 * 2 ^ 59
def prefixEnd_1756230 : Nat := 4983230072969 + 3 ^ 40 * 1756230 * 2
def baseEnd_1756230 : Nat := 601193419897179317165501

theorem tailTrace_1756230 : CollatzResearch.WordTrace tailWord_1756230 prefixEnd_1756230 601193419897179317165501 := by
  unfold tailWord_1756230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001717825858941407801567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42703313618324083366433429 2001717825858941407801567)
  ·
    refine ⟨3002576738788412111702351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001717825858941407801567 3002576738788412111702351)
    ·
      refine ⟨4503865108182618167553527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002576738788412111702351 4503865108182618167553527)
      ·
        refine ⟨6755797662273927251330291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503865108182618167553527 6755797662273927251330291)
        ·
          refine ⟨10133696493410890876995437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755797662273927251330291 10133696493410890876995437)
          ·
            refine ⟨3800136185029084078873289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10133696493410890876995437 3800136185029084078873289)
            ·
              refine ⟨2850102138771813059154967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800136185029084078873289 2850102138771813059154967)
              ·
                refine ⟨4275153208157719588732451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850102138771813059154967 4275153208157719588732451)
                ·
                  refine ⟨6412729812236579383098677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275153208157719588732451 6412729812236579383098677)
                  ·
                    refine ⟨601193419897179317165501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6412729812236579383098677 601193419897179317165501)
                    ·
                      rfl

theorem cell22_1756230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1756230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756230 prefixEnd_1756230 := by exact prefixLift 1756230
  have htrace : WordTrace (prefixWord ++ tailWord_1756230) baseStart_1756230 baseEnd_1756230 := by
    simpa [prefixWord, tailWord_1756230, baseEnd_1756230] using wordTrace_append hprefix tailTrace_1756230
  have hstable : (prefixWord ++ tailWord_1756230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756230).length < 2 ^ (prefixWord ++ tailWord_1756230).sum := by decide
  have hdescent : baseEnd_1756230 < baseStart_1756230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756241 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_1756241 : Nat := 118140960795 + 1756241 * 2 ^ 59
def prefixEnd_1756241 : Nat := 4983230072969 + 3 ^ 40 * 1756241 * 2
def baseEnd_1756241 : Nat := 601197185421978955140467

theorem tailTrace_1756241 : CollatzResearch.WordTrace tailWord_1756241 prefixEnd_1756241 601197185421978955140467 := by
  unfold tailWord_1756241
  simp only [CollatzResearch.WordTrace]
  refine ⟨64055371630446273928300577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42703581086964182618867051 64055371630446273928300577)
  ·
    refine ⟨48041528722834705446225433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64055371630446273928300577 48041528722834705446225433)
    ·
      refine ⟨36031146542126029084669075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48041528722834705446225433 36031146542126029084669075)
      ·
        refine ⟨54046719813189043627003613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36031146542126029084669075 54046719813189043627003613)
        ·
          refine ⟨20267519929945891360126355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54046719813189043627003613 20267519929945891360126355)
          ·
            refine ⟨30401279894918837040189533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20267519929945891360126355 30401279894918837040189533)
            ·
              refine ⟨11400479960594563890071075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30401279894918837040189533 11400479960594563890071075)
              ·
                refine ⟨17100719940891845835106613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11400479960594563890071075 17100719940891845835106613)
                ·
                  refine ⟨1603192494458610547041245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17100719940891845835106613 1603192494458610547041245)
                  ·
                    refine ⟨601197185421978955140467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603192494458610547041245 601197185421978955140467)
                    ·
                      rfl

theorem cell22_1756241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_1756241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756241 prefixEnd_1756241 := by exact prefixLift 1756241
  have htrace : WordTrace (prefixWord ++ tailWord_1756241) baseStart_1756241 baseEnd_1756241 := by
    simpa [prefixWord, tailWord_1756241, baseEnd_1756241] using wordTrace_append hprefix tailTrace_1756241
  have hstable : (prefixWord ++ tailWord_1756241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756241).length < 2 ^ (prefixWord ++ tailWord_1756241).sum := by decide
  have hdescent : baseEnd_1756241 < baseStart_1756241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756264 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1756264 : Nat := 118140960795 + 1756264 * 2 ^ 59
def prefixEnd_1756264 : Nat := 4983230072969 + 3 ^ 40 * 1756264 * 2
def baseEnd_1756264 : Nat := 601205058792014561815397

theorem tailTrace_1756264 : CollatzResearch.WordTrace tailWord_1756264 prefixEnd_1756264 601205058792014561815397 := by
  unfold tailWord_1756264
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028105254681474428193923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42704140339575299237591897 32028105254681474428193923)
  ·
    refine ⟨48042157882022211642290885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32028105254681474428193923 48042157882022211642290885)
    ·
      refine ⟨9007904602879164682929541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48042157882022211642290885 9007904602879164682929541)
      ·
        refine ⟨1688982113039843378049289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9007904602879164682929541 1688982113039843378049289)
        ·
          refine ⟨1266736584779882533536967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688982113039843378049289 1266736584779882533536967)
          ·
            refine ⟨1900104877169823800305451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266736584779882533536967 1900104877169823800305451)
            ·
              refine ⟨2850157315754735700458177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900104877169823800305451 2850157315754735700458177)
              ·
                refine ⟨2137617986816051775343633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850157315754735700458177 2137617986816051775343633)
                ·
                  refine ⟨1603213490112038831507725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2137617986816051775343633 1603213490112038831507725)
                  ·
                    refine ⟨601205058792014561815397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603213490112038831507725 601205058792014561815397)
                    ·
                      rfl

theorem cell22_1756264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1756264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756264 prefixEnd_1756264 := by exact prefixLift 1756264
  have htrace : WordTrace (prefixWord ++ tailWord_1756264) baseStart_1756264 baseEnd_1756264 := by
    simpa [prefixWord, tailWord_1756264, baseEnd_1756264] using wordTrace_append hprefix tailTrace_1756264
  have hstable : (prefixWord ++ tailWord_1756264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756264).length < 2 ^ (prefixWord ++ tailWord_1756264).sum := by decide
  have hdescent : baseEnd_1756264 < baseStart_1756264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756346 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1756346 : Nat := 118140960795 + 1756346 * 2 ^ 59
def prefixEnd_1756346 : Nat := 4983230072969 + 3 ^ 40 * 1756346 * 2
def baseEnd_1756346 : Nat := 601233129067793681265145

theorem tailTrace_1756346 : CollatzResearch.WordTrace tailWord_1756346 prefixEnd_1756346 601233129067793681265145 := by
  unfold tailWord_1756346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014800323766469215218223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42706134196710584573915261 16014800323766469215218223)
  ·
    refine ⟨24022200485649703822827335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16014800323766469215218223 24022200485649703822827335)
    ·
      refine ⟨36033300728474555734241003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24022200485649703822827335 36033300728474555734241003)
      ·
        refine ⟨54049951092711833601361505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36033300728474555734241003 54049951092711833601361505)
        ·
          refine ⟨40537463319533875201021129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54049951092711833601361505 40537463319533875201021129)
          ·
            refine ⟨30403097489650406400765847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40537463319533875201021129 30403097489650406400765847)
            ·
              refine ⟨45604646234475609601148771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30403097489650406400765847 45604646234475609601148771)
              ·
                refine ⟨68406969351713414401723157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45604646234475609601148771 68406969351713414401723157)
                ·
                  refine ⟨3206576688361566300080773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68406969351713414401723157 3206576688361566300080773)
                  ·
                    refine ⟨601233129067793681265145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206576688361566300080773 601233129067793681265145)
                    ·
                      rfl

theorem cell22_1756346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1756346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756346 prefixEnd_1756346 := by exact prefixLift 1756346
  have htrace : WordTrace (prefixWord ++ tailWord_1756346) baseStart_1756346 baseEnd_1756346 := by
    simpa [prefixWord, tailWord_1756346, baseEnd_1756346] using wordTrace_append hprefix tailTrace_1756346
  have hstable : (prefixWord ++ tailWord_1756346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756346).length < 2 ^ (prefixWord ++ tailWord_1756346).sum := by decide
  have hdescent : baseEnd_1756346 < baseStart_1756346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756352 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_1756352 : Nat := 118140960795 + 1756352 * 2 ^ 59
def prefixEnd_1756352 : Nat := 4983230072969 + 3 ^ 40 * 1756352 * 2
def baseEnd_1756352 : Nat := 601235182990411665615127

theorem tailTrace_1756352 : CollatzResearch.WordTrace tailWord_1756352 prefixEnd_1756352 601235182990411665615127 := by
  unfold tailWord_1756352
  simp only [CollatzResearch.WordTrace]
  refine ⟨32029710066522069942795655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42706280088696093257060873 32029710066522069942795655)
  ·
    refine ⟨48044565099783104914193483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32029710066522069942795655 48044565099783104914193483)
    ·
      refine ⟨72066847649674657371290225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48044565099783104914193483 72066847649674657371290225)
      ·
        refine ⟨54050135737255993028467669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72066847649674657371290225 54050135737255993028467669)
        ·
          refine ⟨1266800056341937336604711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54050135737255993028467669 1266800056341937336604711)
          ·
            refine ⟨1900200084512906004907067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266800056341937336604711 1900200084512906004907067)
            ·
              refine ⟨2850300126769359007360601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900200084512906004907067 2850300126769359007360601)
              ·
                refine ⟨2137725095077019255520451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850300126769359007360601 2137725095077019255520451)
                ·
                  refine ⟨3206587642615528883280677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137725095077019255520451 3206587642615528883280677)
                  ·
                    refine ⟨601235182990411665615127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3206587642615528883280677 601235182990411665615127)
                    ·
                      rfl

theorem cell22_1756352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_1756352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756352 prefixEnd_1756352 := by exact prefixLift 1756352
  have htrace : WordTrace (prefixWord ++ tailWord_1756352) baseStart_1756352 baseEnd_1756352 := by
    simpa [prefixWord, tailWord_1756352, baseEnd_1756352] using wordTrace_append hprefix tailTrace_1756352
  have hstable : (prefixWord ++ tailWord_1756352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756352).length < 2 ^ (prefixWord ++ tailWord_1756352).sum := by decide
  have hdescent : baseEnd_1756352 < baseStart_1756352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756421 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1756421 : Nat := 118140960795 + 1756421 * 2 ^ 59
def prefixEnd_1756421 : Nat := 4983230072969 + 3 ^ 40 * 1756421 * 2
def baseEnd_1756421 : Nat := 601258803100518485639915

theorem tailTrace_1756421 : CollatzResearch.WordTrace tailWord_1756421 prefixEnd_1756421 601258803100518485639915 := by
  unfold tailWord_1756421
  simp only [CollatzResearch.WordTrace]
  refine ⟨64061936769794164669853117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42707957846529443113235411 64061936769794164669853117)
  ·
    refine ⟨24023226288672811751194919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64061936769794164669853117 24023226288672811751194919)
    ·
      refine ⟨36034839433009217626792379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24023226288672811751194919 36034839433009217626792379)
      ·
        refine ⟨54052259149513826440188569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36034839433009217626792379 54052259149513826440188569)
        ·
          refine ⟨40539194362135369830141427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54052259149513826440188569 40539194362135369830141427)
          ·
            refine ⟨60808791543203054745212141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40539194362135369830141427 60808791543203054745212141)
            ·
              refine ⟨22803296828701145529454553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60808791543203054745212141 22803296828701145529454553)
              ·
                refine ⟨17102472621525859147090915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22803296828701145529454553 17102472621525859147090915)
                ·
                  refine ⟨25653708932288788720636373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17102472621525859147090915 25653708932288788720636373)
                  ·
                    refine ⟨601258803100518485639915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25653708932288788720636373 601258803100518485639915)
                    ·
                      rfl

theorem cell22_1756421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1756421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756421 prefixEnd_1756421 := by exact prefixLift 1756421
  have htrace : WordTrace (prefixWord ++ tailWord_1756421) baseStart_1756421 baseEnd_1756421 := by
    simpa [prefixWord, tailWord_1756421, baseEnd_1756421] using wordTrace_append hprefix tailTrace_1756421
  have hstable : (prefixWord ++ tailWord_1756421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756421).length < 2 ^ (prefixWord ++ tailWord_1756421).sum := by decide
  have hdescent : baseEnd_1756421 < baseStart_1756421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756427 : List Nat := [1, 1, 1, 1, 5, 4, 2, 3, 1, 3]
def baseStart_1756427 : Nat := 118140960795 + 1756427 * 2 ^ 59
def prefixEnd_1756427 : Nat := 4983230072969 + 3 ^ 40 * 1756427 * 2
def baseEnd_1756427 : Nat := 601260857023136469989897

theorem tailTrace_1756427 : CollatzResearch.WordTrace tailWord_1756427 prefixEnd_1756427 601260857023136469989897 := by
  unfold tailWord_1756427
  simp only [CollatzResearch.WordTrace]
  refine ⟨64062155607772427694571535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42708103738514951796381023 64062155607772427694571535)
  ·
    refine ⟨96093233411658641541857303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64062155607772427694571535 96093233411658641541857303)
    ·
      refine ⟨144139850117487962312785955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96093233411658641541857303 144139850117487962312785955)
      ·
        refine ⟨216209775176231943469178933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144139850117487962312785955 216209775176231943469178933)
        ·
          refine ⟨20269666422771744700235525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216209775176231943469178933 20269666422771744700235525)
          ·
            refine ⟨3800562454269702131294161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20269666422771744700235525 3800562454269702131294161)
            ·
              refine ⟨2850421840702276598470621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800562454269702131294161 2850421840702276598470621)
              ·
                refine ⟨1068908190263353724426483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2850421840702276598470621 1068908190263353724426483)
                ·
                  refine ⟨1603362285395030586639725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068908190263353724426483 1603362285395030586639725)
                  ·
                    refine ⟨601260857023136469989897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603362285395030586639725 601260857023136469989897)
                    ·
                      rfl

theorem cell22_1756427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 1, 3].length) (baseStart_1756427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756427 prefixEnd_1756427 := by exact prefixLift 1756427
  have htrace : WordTrace (prefixWord ++ tailWord_1756427) baseStart_1756427 baseEnd_1756427 := by
    simpa [prefixWord, tailWord_1756427, baseEnd_1756427] using wordTrace_append hprefix tailTrace_1756427
  have hstable : (prefixWord ++ tailWord_1756427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756427).length < 2 ^ (prefixWord ++ tailWord_1756427).sum := by decide
  have hdescent : baseEnd_1756427 < baseStart_1756427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756440 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_1756440 : Nat := 118140960795 + 1756440 * 2 ^ 59
def prefixEnd_1756440 : Nat := 4983230072969 + 3 ^ 40 * 1756440 * 2
def baseEnd_1756440 : Nat := 200421769062936256471619

theorem tailTrace_1756440 : CollatzResearch.WordTrace tailWord_1756440 prefixEnd_1756440 200421769062936256471619 := by
  unfold tailWord_1756440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32031314878362665457397387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42708419837816887276529849 32031314878362665457397387)
  ·
    refine ⟨48046972317543998186096081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32031314878362665457397387 48046972317543998186096081)
    ·
      refine ⟨36035229238157998639572061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48046972317543998186096081 36035229238157998639572061)
      ·
        refine ⟨13513210964309249489839523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36035229238157998639572061 13513210964309249489839523)
        ·
          refine ⟨20269816446463874234759285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513210964309249489839523 20269816446463874234759285)
          ·
            refine ⟨1900295291855988209508683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20269816446463874234759285 1900295291855988209508683)
            ·
              refine ⟨2850442937783982314263025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900295291855988209508683 2850442937783982314263025)
              ·
                refine ⟨2137832203337986735697269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850442937783982314263025 2137832203337986735697269)
                ·
                  refine ⟨200421769062936256471619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2137832203337986735697269 200421769062936256471619)
                  ·
                    rfl

theorem cell22_1756440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_1756440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756440 prefixEnd_1756440 := by exact prefixLift 1756440
  have htrace : WordTrace (prefixWord ++ tailWord_1756440) baseStart_1756440 baseEnd_1756440 := by
    simpa [prefixWord, tailWord_1756440, baseEnd_1756440] using wordTrace_append hprefix tailTrace_1756440
  have hstable : (prefixWord ++ tailWord_1756440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756440).length < 2 ^ (prefixWord ++ tailWord_1756440).sum := by decide
  have hdescent : baseEnd_1756440 < baseStart_1756440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756500 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_1756500 : Nat := 118140960795 + 1756500 * 2 ^ 59
def prefixEnd_1756500 : Nat := 4983230072969 + 3 ^ 40 * 1756500 * 2
def baseEnd_1756500 : Nat := 601285846414988612914673

theorem tailTrace_1756500 : CollatzResearch.WordTrace tailWord_1756500 prefixEnd_1756500 601285846414988612914673 := by
  unfold tailWord_1756500
  simp only [CollatzResearch.WordTrace]
  refine ⟨32032409068253980580989477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42709878757671974107985969 32032409068253980580989477)
  ·
    refine ⟨6006076700297621358935527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32032409068253980580989477 6006076700297621358935527)
    ·
      refine ⟨9009115050446432038403291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6006076700297621358935527 9009115050446432038403291)
      ·
        refine ⟨13513672575669648057604937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009115050446432038403291 13513672575669648057604937)
        ·
          refine ⟨10135254431752236043203703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13513672575669648057604937 10135254431752236043203703)
          ·
            refine ⟨15202881647628354064805555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135254431752236043203703 15202881647628354064805555)
            ·
              refine ⟨22804322471442531097208333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15202881647628354064805555 22804322471442531097208333)
              ·
                refine ⟨8551620926790949161453125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22804322471442531097208333 8551620926790949161453125)
                ·
                  refine ⟨1603428923773302967772461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8551620926790949161453125 1603428923773302967772461)
                  ·
                    refine ⟨601285846414988612914673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603428923773302967772461 601285846414988612914673)
                    ·
                      rfl

theorem cell22_1756500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_1756500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756500 prefixEnd_1756500 := by exact prefixLift 1756500
  have htrace : WordTrace (prefixWord ++ tailWord_1756500) baseStart_1756500 baseEnd_1756500 := by
    simpa [prefixWord, tailWord_1756500, baseEnd_1756500] using wordTrace_append hprefix tailTrace_1756500
  have hstable : (prefixWord ++ tailWord_1756500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756500).length < 2 ^ (prefixWord ++ tailWord_1756500).sum := by decide
  have hdescent : baseEnd_1756500 < baseStart_1756500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756575 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 5]
def baseStart_1756575 : Nat := 118140960795 + 1756575 * 2 ^ 59
def prefixEnd_1756575 : Nat := 4983230072969 + 3 ^ 40 * 1756575 * 2
def baseEnd_1756575 : Nat := 200437173482571139096481

theorem tailTrace_1756575 : CollatzResearch.WordTrace tailWord_1756575 prefixEnd_1756575 200437173482571139096481 := by
  unfold tailWord_1756575
  simp only [CollatzResearch.WordTrace]
  refine ⟨64067553611236248970959179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42711702407490832647306119 64067553611236248970959179)
  ·
    refine ⟨96101330416854373456438769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64067553611236248970959179 96101330416854373456438769)
    ·
      refine ⟨72075997812640780092329077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96101330416854373456438769 72075997812640780092329077)
      ·
        refine ⟨6757124794935073133655851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72075997812640780092329077 6757124794935073133655851)
        ·
          refine ⟨10135687192402609700483777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757124794935073133655851 10135687192402609700483777)
          ·
            refine ⟨7601765394301957275362833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10135687192402609700483777 7601765394301957275362833)
            ·
              refine ⟨5701324045726467956522125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7601765394301957275362833 5701324045726467956522125)
              ·
                refine ⟨2137996517147425483695797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5701324045726467956522125 2137996517147425483695797)
                ·
                  refine ⟨200437173482571139096481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2137996517147425483695797 200437173482571139096481)
                  ·
                    rfl

theorem cell22_1756575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 5].length) (baseStart_1756575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756575 prefixEnd_1756575 := by exact prefixLift 1756575
  have htrace : WordTrace (prefixWord ++ tailWord_1756575) baseStart_1756575 baseEnd_1756575 := by
    simpa [prefixWord, tailWord_1756575, baseEnd_1756575] using wordTrace_append hprefix tailTrace_1756575
  have hstable : (prefixWord ++ tailWord_1756575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756575).length < 2 ^ (prefixWord ++ tailWord_1756575).sum := by decide
  have hdescent : baseEnd_1756575 < baseStart_1756575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756620 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_1756620 : Nat := 118140960795 + 1756620 * 2 ^ 59
def prefixEnd_1756620 : Nat := 4983230072969 + 3 ^ 40 * 1756620 * 2
def baseEnd_1756620 : Nat := 200442308289116099971435

theorem tailTrace_1756620 : CollatzResearch.WordTrace tailWord_1756620 prefixEnd_1756620 200442308289116099971435 := by
  unfold tailWord_1756620
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034597448036610828173657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42712796597382147770898209 32034597448036610828173657)
  ·
    refine ⟨24025948086027458121130243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32034597448036610828173657 24025948086027458121130243)
    ·
      refine ⟨36038922129041187181695365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24025948086027458121130243 36038922129041187181695365)
      ·
        refine ⟨6757297899195222596567881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36038922129041187181695365 6757297899195222596567881)
        ·
          refine ⟨5067973424396416947425911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6757297899195222596567881 5067973424396416947425911)
          ·
            refine ⟨7601960136594625421138867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067973424396416947425911 7601960136594625421138867)
            ·
              refine ⟨11402940204891938131708301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7601960136594625421138867 11402940204891938131708301)
              ·
                refine ⟨4276102576834476799390613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11402940204891938131708301 4276102576834476799390613)
                ·
                  refine ⟨200442308289116099971435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4276102576834476799390613 200442308289116099971435)
                  ·
                    rfl

theorem cell22_1756620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_1756620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756620 prefixEnd_1756620 := by exact prefixLift 1756620
  have htrace : WordTrace (prefixWord ++ tailWord_1756620) baseStart_1756620 baseEnd_1756620 := by
    simpa [prefixWord, tailWord_1756620, baseEnd_1756620] using wordTrace_append hprefix tailTrace_1756620
  have hstable : (prefixWord ++ tailWord_1756620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756620).length < 2 ^ (prefixWord ++ tailWord_1756620).sum := by decide
  have hdescent : baseEnd_1756620 < baseStart_1756620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756727 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 5]
def baseStart_1756727 : Nat := 118140960795 + 1756727 * 2 ^ 59
def prefixEnd_1756727 : Nat := 4983230072969 + 3 ^ 40 * 1756727 * 2
def baseEnd_1756727 : Nat := 200454517718011895829659

theorem tailTrace_1756727 : CollatzResearch.WordTrace tailWord_1756727 prefixEnd_1756727 200454517718011895829659 := by
  unfold tailWord_1756727
  simp only [CollatzResearch.WordTrace]
  refine ⟨64073097506685578930492435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42715398337790385953661623 64073097506685578930492435)
  ·
    refine ⟨96109646260028368395738653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64073097506685578930492435 96109646260028368395738653)
    ·
      refine ⟨36041117347510638148401995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96109646260028368395738653 36041117347510638148401995)
      ·
        refine ⟨54061676021265957222602993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36041117347510638148401995 54061676021265957222602993)
        ·
          refine ⟨40546257015949467916952245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54061676021265957222602993 40546257015949467916952245)
          ·
            refine ⟨3801211595245262617214273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40546257015949467916952245 3801211595245262617214273)
            ·
              refine ⟨2850908696433946962910705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801211595245262617214273 2850908696433946962910705)
              ·
                refine ⟨2138181522325460222183029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850908696433946962910705 2138181522325460222183029)
                ·
                  refine ⟨200454517718011895829659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2138181522325460222183029 200454517718011895829659)
                  ·
                    rfl

theorem cell22_1756727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 5].length) (baseStart_1756727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756727 prefixEnd_1756727 := by exact prefixLift 1756727
  have htrace : WordTrace (prefixWord ++ tailWord_1756727) baseStart_1756727 baseEnd_1756727 := by
    simpa [prefixWord, tailWord_1756727, baseEnd_1756727] using wordTrace_append hprefix tailTrace_1756727
  have hstable : (prefixWord ++ tailWord_1756727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756727).length < 2 ^ (prefixWord ++ tailWord_1756727).sum := by decide
  have hdescent : baseEnd_1756727 < baseStart_1756727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756757 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1756757 : Nat := 118140960795 + 1756757 * 2 ^ 59
def prefixEnd_1756757 : Nat := 4983230072969 + 3 ^ 40 * 1756757 * 2
def baseEnd_1756757 : Nat := 601373822767125609238885

theorem tailTrace_1756757 : CollatzResearch.WordTrace tailWord_1756757 prefixEnd_1756757 601373822767125609238885 := by
  unfold tailWord_1756757
  simp only [CollatzResearch.WordTrace]
  refine ⟨64074191696576894054084525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42716127797717929369389683 64074191696576894054084525)
  ·
    refine ⟨24027821886216335270281697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64074191696576894054084525 24027821886216335270281697)
    ·
      refine ⟨18020866414662251452711273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24027821886216335270281697 18020866414662251452711273)
      ·
        refine ⟨13515649810996688589533455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18020866414662251452711273 13515649810996688589533455)
        ·
          refine ⟨20273474716495032884300183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13515649810996688589533455 20273474716495032884300183)
          ·
            refine ⟨30410212074742549326450275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20273474716495032884300183 30410212074742549326450275)
            ·
              refine ⟨45615318112113823989675413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30410212074742549326450275 45615318112113823989675413)
              ·
                refine ⟨2138218036505335499516035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45615318112113823989675413 2138218036505335499516035)
                ·
                  refine ⟨3207327054758003249274053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2138218036505335499516035 3207327054758003249274053)
                  ·
                    refine ⟨601373822767125609238885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3207327054758003249274053 601373822767125609238885)
                    ·
                      rfl

theorem cell22_1756757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1756757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756757 prefixEnd_1756757 := by exact prefixLift 1756757
  have htrace : WordTrace (prefixWord ++ tailWord_1756757) baseStart_1756757 baseEnd_1756757 := by
    simpa [prefixWord, tailWord_1756757, baseEnd_1756757] using wordTrace_append hprefix tailTrace_1756757
  have hstable : (prefixWord ++ tailWord_1756757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756757).length < 2 ^ (prefixWord ++ tailWord_1756757).sum := by decide
  have hdescent : baseEnd_1756757 < baseStart_1756757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756765 : List Nat := [1, 4, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1756765 : Nat := 118140960795 + 1756765 * 2 ^ 59
def prefixEnd_1756765 : Nat := 4983230072969 + 3 ^ 40 * 1756765 * 2
def baseEnd_1756765 : Nat := 601376561330616255038861

theorem tailTrace_1756765 : CollatzResearch.WordTrace tailWord_1756765 prefixEnd_1756765 601376561330616255038861 := by
  unfold tailWord_1756765
  simp only [CollatzResearch.WordTrace]
  refine ⟨64074483480547911420375749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42716322320365274280250499 64074483480547911420375749)
  ·
    refine ⟨12013965652602733391320453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64074483480547911420375749 12013965652602733391320453)
    ·
      refine ⟨2252618559863012510872585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12013965652602733391320453 2252618559863012510872585)
      ·
        refine ⟨1689463919897259383154439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2252618559863012510872585 1689463919897259383154439)
        ·
          refine ⟨2534195879845889074731659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689463919897259383154439 2534195879845889074731659)
          ·
            refine ⟨3801293819768833612097489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534195879845889074731659 3801293819768833612097489)
            ·
              refine ⟨2850970364826625209073117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801293819768833612097489 2850970364826625209073117)
              ·
                refine ⟨1069113886809984453402419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2850970364826625209073117 1069113886809984453402419)
                ·
                  refine ⟨1603670830214976680103629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1069113886809984453402419 1603670830214976680103629)
                  ·
                    refine ⟨601376561330616255038861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1603670830214976680103629 601376561330616255038861)
                    ·
                      rfl

theorem cell22_1756765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1756765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756765 prefixEnd_1756765 := by exact prefixLift 1756765
  have htrace : WordTrace (prefixWord ++ tailWord_1756765) baseStart_1756765 baseEnd_1756765 := by
    simpa [prefixWord, tailWord_1756765, baseEnd_1756765] using wordTrace_append hprefix tailTrace_1756765
  have hstable : (prefixWord ++ tailWord_1756765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756765).length < 2 ^ (prefixWord ++ tailWord_1756765).sum := by decide
  have hdescent : baseEnd_1756765 < baseStart_1756765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756789 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1756789 : Nat := 118140960795 + 1756789 * 2 ^ 59
def prefixEnd_1756789 : Nat := 4983230072969 + 3 ^ 40 * 1756789 * 2
def baseEnd_1756789 : Nat := 200461592340362730812929

theorem tailTrace_1756789 : CollatzResearch.WordTrace tailWord_1756789 prefixEnd_1756789 200461592340362730812929 := by
  unfold tailWord_1756789
  simp only [CollatzResearch.WordTrace]
  refine ⟨64075358832460963519249421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42716905888307309012832947 64075358832460963519249421)
  ·
    refine ⟨24028259562172861319718533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64075358832460963519249421 24028259562172861319718533)
    ·
      refine ⟨4505298667907411497447225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24028259562172861319718533 4505298667907411497447225)
      ·
        refine ⟨3378974000930558623085419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4505298667907411497447225 3378974000930558623085419)
        ·
          refine ⟨5068461001395837934628129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378974000930558623085419 5068461001395837934628129)
          ·
            refine ⟨3801345751046878450971097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5068461001395837934628129 3801345751046878450971097)
            ·
              refine ⟨2851009313285158838228323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801345751046878450971097 2851009313285158838228323)
              ·
                refine ⟨4276513969927738257342485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851009313285158838228323 4276513969927738257342485)
                ·
                  refine ⟨200461592340362730812929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4276513969927738257342485 200461592340362730812929)
                  ·
                    rfl

theorem cell22_1756789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1756789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1756789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1756789 prefixEnd_1756789 := by exact prefixLift 1756789
  have htrace : WordTrace (prefixWord ++ tailWord_1756789) baseStart_1756789 baseEnd_1756789 := by
    simpa [prefixWord, tailWord_1756789, baseEnd_1756789] using wordTrace_append hprefix tailTrace_1756789
  have hstable : (prefixWord ++ tailWord_1756789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756789).length < 2 ^ (prefixWord ++ tailWord_1756789).sum := by decide
  have hdescent : baseEnd_1756789 < baseStart_1756789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
