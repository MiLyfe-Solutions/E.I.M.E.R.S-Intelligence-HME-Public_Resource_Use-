import V185TrunkScan23Chunk0320

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1897562 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1897562 : Nat := 118140960795 + 1897562 * 2 ^ 59
def prefixEnd_1897562 : Nat := 4983230072969 + 3 ^ 40 * 1897562 * 2
def baseEnd_1897562 : Nat := 974361377707010013648277

theorem tailTrace_1897562 : CollatzResearch.WordTrace tailWord_1897562 prefixEnd_1897562 974361377707010013648277 := by
  unfold tailWord_1897562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302442987866106658389735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46139847967642951089039293 17302442987866106658389735)
  ·
    refine ⟨25953664481799159987584603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17302442987866106658389735 25953664481799159987584603)
    ·
      refine ⟨38930496722698739981376905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25953664481799159987584603 38930496722698739981376905)
      ·
        refine ⟨29197872542024054986032679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38930496722698739981376905 29197872542024054986032679)
        ·
          refine ⟨43796808813036082479049019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29197872542024054986032679 43796808813036082479049019)
          ·
            refine ⟨65695213219554123718573529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43796808813036082479049019 65695213219554123718573529)
            ·
              refine ⟨49271409914665592788930147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65695213219554123718573529 49271409914665592788930147)
              ·
                refine ⟨73907114871998389183395221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49271409914665592788930147 73907114871998389183395221)
                ·
                  refine ⟨3464396009624924492971651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73907114871998389183395221 3464396009624924492971651)
                  ·
                    refine ⟨5196594014437386739457477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464396009624924492971651 5196594014437386739457477)
                    ·
                      refine ⟨974361377707010013648277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5196594014437386739457477 974361377707010013648277)
                      ·
                        rfl

theorem cell23_1897562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1897562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897562 prefixEnd_1897562 := by exact prefixLift 1897562
  have htrace : WordTrace (prefixWord ++ tailWord_1897562) baseStart_1897562 baseEnd_1897562 := by
    simpa [prefixWord, tailWord_1897562, baseEnd_1897562] using wordTrace_append hprefix tailTrace_1897562
  have hstable : (prefixWord ++ tailWord_1897562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897562).length < 2 ^ (prefixWord ++ tailWord_1897562).sum := by decide
  have hdescent : baseEnd_1897562 < baseStart_1897562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897619 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 6]
def baseStart_1897619 : Nat := 118140960795 + 1897619 * 2 ^ 59
def prefixEnd_1897619 : Nat := 4983230072969 + 3 ^ 40 * 1897619 * 2
def baseEnd_1897619 : Nat := 108265627344924032292835

theorem tailTrace_1897619 : CollatzResearch.WordTrace tailWord_1897619 prefixEnd_1897619 108265627344924032292835 := by
  unfold tailWord_1897619
  simp only [CollatzResearch.WordTrace]
  refine ⟨69211850912257925368383911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46141233941505283578922607 69211850912257925368383911)
  ·
    refine ⟨103817776368386888052575867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69211850912257925368383911 103817776368386888052575867)
    ·
      refine ⟨155726664552580332078863801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103817776368386888052575867 155726664552580332078863801)
      ·
        refine ⟨116794998414435249059147851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155726664552580332078863801 116794998414435249059147851)
        ·
          refine ⟨175192497621652873588721777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116794998414435249059147851 175192497621652873588721777)
          ·
            refine ⟨131394373216239655191541333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175192497621652873588721777 131394373216239655191541333)
            ·
              refine ⟨1539777811127808459275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 131394373216239655191541333 1539777811127808459275875)
              ·
                refine ⟨2309666716691712688913813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539777811127808459275875 2309666716691712688913813)
                ·
                  refine ⟨108265627344924032292835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2309666716691712688913813 108265627344924032292835)
                  ·
                    rfl

theorem cell23_1897619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 6].length) (baseStart_1897619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897619 prefixEnd_1897619 := by exact prefixLift 1897619
  have htrace : WordTrace (prefixWord ++ tailWord_1897619) baseStart_1897619 baseEnd_1897619 := by
    simpa [prefixWord, tailWord_1897619, baseEnd_1897619] using wordTrace_append hprefix tailTrace_1897619
  have hstable : (prefixWord ++ tailWord_1897619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897619).length < 2 ^ (prefixWord ++ tailWord_1897619).sum := by decide
  have hdescent : baseEnd_1897619 < baseStart_1897619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897669 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 6, 2]
def baseStart_1897669 : Nat := 118140960795 + 1897669 * 2 ^ 59
def prefixEnd_1897669 : Nat := 4983230072969 + 3 ^ 40 * 1897669 * 2
def baseEnd_1897669 : Nat := 974416320137041095010285

theorem tailTrace_1897669 : CollatzResearch.WordTrace tailWord_1897669 prefixEnd_1897669 974416320137041095010285 := by
  unfold tailWord_1897669
  simp only [CollatzResearch.WordTrace]
  refine ⟨69213674562076783907704061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46142449708051189271802707 69213674562076783907704061)
  ·
    refine ⟨25955127960778793965389023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69213674562076783907704061 25955127960778793965389023)
    ·
      refine ⟨38932691941168190948083535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25955127960778793965389023 38932691941168190948083535)
      ·
        refine ⟨58399037911752286422125303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38932691941168190948083535 58399037911752286422125303)
        ·
          refine ⟨87598556867628429633187955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58399037911752286422125303 87598556867628429633187955)
          ·
            refine ⟨131397835301442644449781933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87598556867628429633187955 131397835301442644449781933)
            ·
              refine ⟨49274188238040991668668225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131397835301442644449781933 49274188238040991668668225)
              ·
                refine ⟨36955641178530743751501169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49274188238040991668668225 36955641178530743751501169)
                ·
                  refine ⟨27716730883898057813625877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36955641178530743751501169 27716730883898057813625877)
                  ·
                    refine ⟨1299221760182721460013713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27716730883898057813625877 1299221760182721460013713)
                    ·
                      refine ⟨974416320137041095010285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299221760182721460013713 974416320137041095010285)
                      ·
                        rfl

theorem cell23_1897669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_1897669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897669 prefixEnd_1897669 := by exact prefixLift 1897669
  have htrace : WordTrace (prefixWord ++ tailWord_1897669) baseStart_1897669 baseEnd_1897669 := by
    simpa [prefixWord, tailWord_1897669, baseEnd_1897669] using wordTrace_append hprefix tailTrace_1897669
  have hstable : (prefixWord ++ tailWord_1897669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897669).length < 2 ^ (prefixWord ++ tailWord_1897669).sum := by decide
  have hdescent : baseEnd_1897669 < baseStart_1897669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897703 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1897703 : Nat := 118140960795 + 1897703 * 2 ^ 59
def prefixEnd_1897703 : Nat := 4983230072969 + 3 ^ 40 * 1897703 * 2
def baseEnd_1897703 : Nat := 974433778479293961985129

theorem tailTrace_1897703 : CollatzResearch.WordTrace tailWord_1897703 prefixEnd_1897703 974433778479293961985129 := by
  unfold tailWord_1897703
  simp only [CollatzResearch.WordTrace]
  refine ⟨69214914643953607714441763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46143276429302405142961175 69214914643953607714441763)
  ·
    refine ⟨103822371965930411571662645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69214914643953607714441763 103822371965930411571662645)
    ·
      refine ⟨9733347371805976084843373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103822371965930411571662645 9733347371805976084843373)
      ·
        refine ⟨3650005264427241031816265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9733347371805976084843373 3650005264427241031816265)
        ·
          refine ⟨2737503948320430773862199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650005264427241031816265 2737503948320430773862199)
          ·
            refine ⟨4106255922480646160793299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737503948320430773862199 4106255922480646160793299)
            ·
              refine ⟨6159383883720969241189949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106255922480646160793299 6159383883720969241189949)
              ·
                refine ⟨2309768956395363465446231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6159383883720969241189949 2309768956395363465446231)
                ·
                  refine ⟨3464653434593045198169347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309768956395363465446231 3464653434593045198169347)
                  ·
                    refine ⟨5196980151889567797254021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3464653434593045198169347 5196980151889567797254021)
                    ·
                      refine ⟨974433778479293961985129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5196980151889567797254021 974433778479293961985129)
                      ·
                        rfl

theorem cell23_1897703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1897703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897703 prefixEnd_1897703 := by exact prefixLift 1897703
  have htrace : WordTrace (prefixWord ++ tailWord_1897703) baseStart_1897703 baseEnd_1897703 := by
    simpa [prefixWord, tailWord_1897703, baseEnd_1897703] using wordTrace_append hprefix tailTrace_1897703
  have hstable : (prefixWord ++ tailWord_1897703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897703).length < 2 ^ (prefixWord ++ tailWord_1897703).sum := by decide
  have hdescent : baseEnd_1897703 < baseStart_1897703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897709 : List Nat := [1, 5, 1, 2, 2, 2, 10]
def baseStart_1897709 : Nat := 118140960795 + 1897709 * 2 ^ 59
def prefixEnd_1897709 : Nat := 4983230072969 + 3 ^ 40 * 1897709 * 2
def baseEnd_1897709 : Nat := 12030084683496554796421

theorem tailTrace_1897709 : CollatzResearch.WordTrace tailWord_1897709 prefixEnd_1897709 12030084683496554796421 := by
  unfold tailWord_1897709
  simp only [CollatzResearch.WordTrace]
  refine ⟨69215133481931870739160181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46143422321287913826106787 69215133481931870739160181)
  ·
    refine ⟨6488918763931112881796267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69215133481931870739160181 6488918763931112881796267)
    ·
      refine ⟨9733378145896669322694401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488918763931112881796267 9733378145896669322694401)
      ·
        refine ⟨7300033609422501992020801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9733378145896669322694401 7300033609422501992020801)
        ·
          refine ⟨5475025207066876494015601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300033609422501992020801 5475025207066876494015601)
          ·
            refine ⟨4106268905300157370511701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475025207066876494015601 4106268905300157370511701)
            ·
              refine ⟨12030084683496554796421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4106268905300157370511701 12030084683496554796421)
              ·
                rfl

theorem cell23_1897709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 10].length) (baseStart_1897709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897709 prefixEnd_1897709 := by exact prefixLift 1897709
  have htrace : WordTrace (prefixWord ++ tailWord_1897709) baseStart_1897709 baseEnd_1897709 := by
    simpa [prefixWord, tailWord_1897709, baseEnd_1897709] using wordTrace_append hprefix tailTrace_1897709
  have hstable : (prefixWord ++ tailWord_1897709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897709).length < 2 ^ (prefixWord ++ tailWord_1897709).sum := by decide
  have hdescent : baseEnd_1897709 < baseStart_1897709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897712 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1897712 : Nat := 118140960795 + 1897712 * 2 ^ 59
def prefixEnd_1897712 : Nat := 4983230072969 + 3 ^ 40 * 1897712 * 2
def baseEnd_1897712 : Nat := 974438399805184426772587

theorem tailTrace_1897712 : CollatzResearch.WordTrace tailWord_1897712 prefixEnd_1897712 974438399805184426772587 := by
  unfold tailWord_1897712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34607621450460501125759695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46143495267280668167679593 34607621450460501125759695)
  ·
    refine ⟨51911432175690751688639543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34607621450460501125759695 51911432175690751688639543)
    ·
      refine ⟨77867148263536127532959315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51911432175690751688639543 77867148263536127532959315)
      ·
        refine ⟨116800722395304191299438973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77867148263536127532959315 116800722395304191299438973)
        ·
          refine ⟨43800270898239071737289615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116800722395304191299438973 43800270898239071737289615)
          ·
            refine ⟨65700406347358607605934423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43800270898239071737289615 65700406347358607605934423)
            ·
              refine ⟨98550609521037911408901635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65700406347358607605934423 98550609521037911408901635)
              ·
                refine ⟨147825914281556867113352453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98550609521037911408901635 147825914281556867113352453)
                ·
                  refine ⟨27717358927791912583753585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147825914281556867113352453 27717358927791912583753585)
                  ·
                    refine ⟨20788019195843934437815189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27717358927791912583753585 20788019195843934437815189)
                    ·
                      refine ⟨974438399805184426772587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20788019195843934437815189 974438399805184426772587)
                      ·
                        rfl

theorem cell23_1897712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1897712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897712 prefixEnd_1897712 := by exact prefixLift 1897712
  have htrace : WordTrace (prefixWord ++ tailWord_1897712) baseStart_1897712 baseEnd_1897712 := by
    simpa [prefixWord, tailWord_1897712, baseEnd_1897712] using wordTrace_append hprefix tailTrace_1897712
  have hstable : (prefixWord ++ tailWord_1897712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897712).length < 2 ^ (prefixWord ++ tailWord_1897712).sum := by decide
  have hdescent : baseEnd_1897712 < baseStart_1897712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897730 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1897730 : Nat := 118140960795 + 1897730 * 2 ^ 59
def prefixEnd_1897730 : Nat := 4983230072969 + 3 ^ 40 * 1897730 * 2
def baseEnd_1897730 : Nat := 324815880818988452115835

theorem tailTrace_1897730 : CollatzResearch.WordTrace tailWord_1897730 prefixEnd_1897730 324815880818988452115835 := by
  unfold tailWord_1897730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17303974853713947831418661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46143932943237194217116429 17303974853713947831418661)
  ·
    refine ⟨3244495285071365218390999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17303974853713947831418661 3244495285071365218390999)
    ·
      refine ⟨4866742927607047827586499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244495285071365218390999 4866742927607047827586499)
      ·
        refine ⟨7300114391410571741379749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866742927607047827586499 7300114391410571741379749)
        ·
          refine ⟨1368771448389482201508703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7300114391410571741379749 1368771448389482201508703)
          ·
            refine ⟨2053157172584223302263055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368771448389482201508703 2053157172584223302263055)
            ·
              refine ⟨3079735758876334953394583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053157172584223302263055 3079735758876334953394583)
              ·
                refine ⟨4619603638314502430091875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079735758876334953394583 4619603638314502430091875)
                ·
                  refine ⟨6929405457471753645137813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619603638314502430091875 6929405457471753645137813)
                  ·
                    refine ⟨324815880818988452115835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6929405457471753645137813 324815880818988452115835)
                    ·
                      rfl

theorem cell23_1897730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1897730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897730 prefixEnd_1897730 := by exact prefixLift 1897730
  have htrace : WordTrace (prefixWord ++ tailWord_1897730) baseStart_1897730 baseEnd_1897730 := by
    simpa [prefixWord, tailWord_1897730, baseEnd_1897730] using wordTrace_append hprefix tailTrace_1897730
  have hstable : (prefixWord ++ tailWord_1897730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897730).length < 2 ^ (prefixWord ++ tailWord_1897730).sum := by decide
  have hdescent : baseEnd_1897730 < baseStart_1897730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897763 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 1, 3, 2]
def baseStart_1897763 : Nat := 118140960795 + 1897763 * 2 ^ 59
def prefixEnd_1897763 : Nat := 4983230072969 + 3 ^ 40 * 1897763 * 2
def baseEnd_1897763 : Nat := 974464587318563727234853

theorem tailTrace_1897763 : CollatzResearch.WordTrace tailWord_1897763 prefixEnd_1897763 974464587318563727234853 := by
  unfold tailWord_1897763
  simp only [CollatzResearch.WordTrace]
  refine ⟨69217103023736237961625943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46144735349157491974417295 69217103023736237961625943)
  ·
    refine ⟨103825654535604356942438915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69217103023736237961625943 103825654535604356942438915)
    ·
      refine ⟨155738481803406535413658373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103825654535604356942438915 155738481803406535413658373)
      ·
        refine ⟨29200965338138725390060945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155738481803406535413658373 29200965338138725390060945)
        ·
          refine ⟨21900724003604044042545709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29200965338138725390060945 21900724003604044042545709)
          ·
            refine ⟨8212771501351516515954641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21900724003604044042545709 8212771501351516515954641)
            ·
              refine ⟨6159578626013637386965981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8212771501351516515954641 6159578626013637386965981)
              ·
                refine ⟨2309841984755114020112243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6159578626013637386965981 2309841984755114020112243)
                ·
                  refine ⟨3464762977132671030168365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309841984755114020112243 3464762977132671030168365)
                  ·
                    refine ⟨1299286116424751636313137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464762977132671030168365 1299286116424751636313137)
                    ·
                      refine ⟨974464587318563727234853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299286116424751636313137 974464587318563727234853)
                      ·
                        rfl

theorem cell23_1897763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_1897763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897763 prefixEnd_1897763 := by exact prefixLift 1897763
  have htrace : WordTrace (prefixWord ++ tailWord_1897763) baseStart_1897763 baseEnd_1897763 := by
    simpa [prefixWord, tailWord_1897763, baseEnd_1897763] using wordTrace_append hprefix tailTrace_1897763
  have hstable : (prefixWord ++ tailWord_1897763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897763).length < 2 ^ (prefixWord ++ tailWord_1897763).sum := by decide
  have hdescent : baseEnd_1897763 < baseStart_1897763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897816 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 5]
def baseStart_1897816 : Nat := 118140960795 + 1897816 * 2 ^ 59
def prefixEnd_1897816 : Nat := 4983230072969 + 3 ^ 40 * 1897816 * 2
def baseEnd_1897816 : Nat := 108276866865916891096901

theorem tailTrace_1897816 : CollatzResearch.WordTrace tailWord_1897816 prefixEnd_1897816 108276866865916891096901 := by
  unfold tailWord_1897816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34609518046272114006652651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46146024061696152008870201 34609518046272114006652651)
  ·
    refine ⟨51914277069408171009978977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34609518046272114006652651 51914277069408171009978977)
    ·
      refine ⟨38935707802056128257484233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51914277069408171009978977 38935707802056128257484233)
      ·
        refine ⟨29201780851542096193113175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38935707802056128257484233 29201780851542096193113175)
        ·
          refine ⟨43802671277313144289669763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29201780851542096193113175 43802671277313144289669763)
          ·
            refine ⟨65704006915969716434504645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43802671277313144289669763 65704006915969716434504645)
            ·
              refine ⟨12319501296744321831469621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65704006915969716434504645 12319501296744321831469621)
              ·
                refine ⟨1154953246569780171700277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12319501296744321831469621 1154953246569780171700277)
                ·
                  refine ⟨108276866865916891096901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154953246569780171700277 108276866865916891096901)
                  ·
                    rfl

theorem cell23_1897816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 5].length) (baseStart_1897816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897816 prefixEnd_1897816 := by exact prefixLift 1897816
  have htrace : WordTrace (prefixWord ++ tailWord_1897816) baseStart_1897816 baseEnd_1897816 := by
    simpa [prefixWord, tailWord_1897816, baseEnd_1897816] using wordTrace_append hprefix tailTrace_1897816
  have hstable : (prefixWord ++ tailWord_1897816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897816).length < 2 ^ (prefixWord ++ tailWord_1897816).sum := by decide
  have hdescent : baseEnd_1897816 < baseStart_1897816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897839 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_1897839 : Nat := 118140960795 + 1897839 * 2 ^ 59
def prefixEnd_1897839 : Nat := 4983230072969 + 3 ^ 40 * 1897839 * 2
def baseEnd_1897839 : Nat := 974503611848305429884503

theorem tailTrace_1897839 : CollatzResearch.WordTrace tailWord_1897839 prefixEnd_1897839 974503611848305429884503 := by
  unfold tailWord_1897839
  simp only [CollatzResearch.WordTrace]
  refine ⟨69219874971460902941392571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46146583314307268627595047 69219874971460902941392571)
  ·
    refine ⟨103829812457191354412088857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69219874971460902941392571 103829812457191354412088857)
    ·
      refine ⟨77872359342893515809066643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103829812457191354412088857 77872359342893515809066643)
      ·
        refine ⟨116808539014340273713599965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77872359342893515809066643 116808539014340273713599965)
        ·
          refine ⟨43803202130377602642599987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116808539014340273713599965 43803202130377602642599987)
          ·
            refine ⟨65704803195566403963899981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43803202130377602642599987 65704803195566403963899981)
            ·
              refine ⟨24639301198337401486462493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65704803195566403963899981 24639301198337401486462493)
              ·
                refine ⟨9239737949376525557423435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24639301198337401486462493 9239737949376525557423435)
                ·
                  refine ⟨13859606924064788336135153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9239737949376525557423435 13859606924064788336135153)
                  ·
                    refine ⟨10394705193048591252101365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13859606924064788336135153 10394705193048591252101365)
                    ·
                      refine ⟨974503611848305429884503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10394705193048591252101365 974503611848305429884503)
                      ·
                        rfl

theorem cell23_1897839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_1897839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897839 prefixEnd_1897839 := by exact prefixLift 1897839
  have htrace : WordTrace (prefixWord ++ tailWord_1897839) baseStart_1897839 baseEnd_1897839 := by
    simpa [prefixWord, tailWord_1897839, baseEnd_1897839] using wordTrace_append hprefix tailTrace_1897839
  have hstable : (prefixWord ++ tailWord_1897839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897839).length < 2 ^ (prefixWord ++ tailWord_1897839).sum := by decide
  have hdescent : baseEnd_1897839 < baseStart_1897839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897863 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 2, 5]
def baseStart_1897863 : Nat := 118140960795 + 1897863 * 2 ^ 59
def prefixEnd_1897863 : Nat := 4983230072969 + 3 ^ 40 * 1897863 * 2
def baseEnd_1897863 : Nat := 324838645128004445328131

theorem tailTrace_1897863 : CollatzResearch.WordTrace tailWord_1897863 prefixEnd_1897863 324838645128004445328131 := by
  unfold tailWord_1897863
  simp only [CollatzResearch.WordTrace]
  refine ⟨69220750323373955040266243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46147166882249303360177495 69220750323373955040266243)
  ·
    refine ⟨103831125485060932560399365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69220750323373955040266243 103831125485060932560399365)
    ·
      refine ⟨19468336028448924855074881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103831125485060932560399365 19468336028448924855074881)
      ·
        refine ⟨14601252021336693641306161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19468336028448924855074881 14601252021336693641306161)
        ·
          refine ⟨10950939016002520230979621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14601252021336693641306161 10950939016002520230979621)
          ·
            refine ⟨2053301065500472543308679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10950939016002520230979621 2053301065500472543308679)
            ·
              refine ⟨3079951598250708814963019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053301065500472543308679 3079951598250708814963019)
              ·
                refine ⟨4619927397376063222444529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079951598250708814963019 4619927397376063222444529)
                ·
                  refine ⟨3464945548032047416833397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619927397376063222444529 3464945548032047416833397)
                  ·
                    refine ⟨324838645128004445328131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3464945548032047416833397 324838645128004445328131)
                    ·
                      rfl

theorem cell23_1897863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_1897863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897863 prefixEnd_1897863 := by exact prefixLift 1897863
  have htrace : WordTrace (prefixWord ++ tailWord_1897863) baseStart_1897863 baseEnd_1897863 := by
    simpa [prefixWord, tailWord_1897863, baseEnd_1897863] using wordTrace_append hprefix tailTrace_1897863
  have hstable : (prefixWord ++ tailWord_1897863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897863).length < 2 ^ (prefixWord ++ tailWord_1897863).sum := by decide
  have hdescent : baseEnd_1897863 < baseStart_1897863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897919 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 9]
def baseStart_1897919 : Nat := 118140960795 + 1897919 * 2 ^ 59
def prefixEnd_1897919 : Nat := 4983230072969 + 3 ^ 40 * 1897919 * 2
def baseEnd_1897919 : Nat := 324848230100221705628045

theorem tailTrace_1897919 : CollatzResearch.WordTrace tailWord_1897919 prefixEnd_1897919 324848230100221705628045 := by
  unfold tailWord_1897919
  simp only [CollatzResearch.WordTrace]
  refine ⟨69222792811171076604304811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46148528540780717736203207 69222792811171076604304811)
  ·
    refine ⟨103834189216756614906457217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69222792811171076604304811 103834189216756614906457217)
    ·
      refine ⟨77875641912567461179842913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103834189216756614906457217 77875641912567461179842913)
      ·
        refine ⟨58406731434425595884882185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77875641912567461179842913 58406731434425595884882185)
        ·
          refine ⟨43805048575819196913661639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58406731434425595884882185 43805048575819196913661639)
          ·
            refine ⟨65707572863728795370492459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43805048575819196913661639 65707572863728795370492459)
            ·
              refine ⟨98561359295593193055738689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65707572863728795370492459 98561359295593193055738689)
              ·
                refine ⟨73921019471694894791804017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98561359295593193055738689 73921019471694894791804017)
                ·
                  refine ⟨55440764603771171093853013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73921019471694894791804017 55440764603771171093853013)
                  ·
                    refine ⟨324848230100221705628045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55440764603771171093853013 324848230100221705628045)
                    ·
                      rfl

theorem cell23_1897919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_1897919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897919 prefixEnd_1897919 := by exact prefixLift 1897919
  have htrace : WordTrace (prefixWord ++ tailWord_1897919) baseStart_1897919 baseEnd_1897919 := by
    simpa [prefixWord, tailWord_1897919, baseEnd_1897919] using wordTrace_append hprefix tailTrace_1897919
  have hstable : (prefixWord ++ tailWord_1897919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897919).length < 2 ^ (prefixWord ++ tailWord_1897919).sum := by decide
  have hdescent : baseEnd_1897919 < baseStart_1897919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897939 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_1897939 : Nat := 118140960795 + 1897939 * 2 ^ 59
def prefixEnd_1897939 : Nat := 4983230072969 + 3 ^ 40 * 1897939 * 2
def baseEnd_1897939 : Nat := 974554959913755038634043

theorem tailTrace_1897939 : CollatzResearch.WordTrace tailWord_1897939 prefixEnd_1897939 974554959913755038634043 := by
  unfold tailWord_1897939
  simp only [CollatzResearch.WordTrace]
  refine ⟨69223522271098620020032871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46149014847399080013355247 69223522271098620020032871)
  ·
    refine ⟨103835283406647930030049307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69223522271098620020032871 103835283406647930030049307)
    ·
      refine ⟨155752925109971895045073961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103835283406647930030049307 155752925109971895045073961)
      ·
        refine ⟨116814693832478921283805471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155752925109971895045073961 116814693832478921283805471)
        ·
          refine ⟨175222040748718381925708207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116814693832478921283805471 175222040748718381925708207)
          ·
            refine ⟨262833061123077572888562311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175222040748718381925708207 262833061123077572888562311)
            ·
              refine ⟨394249591684616359332843467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262833061123077572888562311 394249591684616359332843467)
              ·
                refine ⟨591374387526924538999265201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394249591684616359332843467 591374387526924538999265201)
                ·
                  refine ⟨443530790645193404249448901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 591374387526924538999265201 443530790645193404249448901)
                  ·
                    refine ⟨83162023245973763296771669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 443530790645193404249448901 83162023245973763296771669)
                    ·
                      refine ⟨974554959913755038634043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 83162023245973763296771669 974554959913755038634043)
                      ·
                        rfl

theorem cell23_1897939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_1897939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897939 prefixEnd_1897939 := by exact prefixLift 1897939
  have htrace : WordTrace (prefixWord ++ tailWord_1897939) baseStart_1897939 baseEnd_1897939 := by
    simpa [prefixWord, tailWord_1897939, baseEnd_1897939] using wordTrace_append hprefix tailTrace_1897939
  have hstable : (prefixWord ++ tailWord_1897939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897939).length < 2 ^ (prefixWord ++ tailWord_1897939).sum := by decide
  have hdescent : baseEnd_1897939 < baseStart_1897939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897970 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_1897970 : Nat := 118140960795 + 1897970 * 2 ^ 59
def prefixEnd_1897970 : Nat := 4983230072969 + 3 ^ 40 * 1897970 * 2
def baseEnd_1897970 : Nat := 324856959271348139115467

theorem tailTrace_1897970 : CollatzResearch.WordTrace tailWord_1897970 prefixEnd_1897970 324856959271348139115467 := by
  unfold tailWord_1897970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17306163233496578078602841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46149768622657541542940909 17306163233496578078602841)
  ·
    refine ⟨12979622425122433558952131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17306163233496578078602841 12979622425122433558952131)
    ·
      refine ⟨19469433637683650338428197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12979622425122433558952131 19469433637683650338428197)
      ·
        refine ⟨3650518807065684438455287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19469433637683650338428197 3650518807065684438455287)
        ·
          refine ⟨5475778210598526657682931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650518807065684438455287 5475778210598526657682931)
          ·
            refine ⟨8213667315897789986524397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475778210598526657682931 8213667315897789986524397)
            ·
              refine ⟨3080125243461671244946649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8213667315897789986524397 3080125243461671244946649)
              ·
                refine ⟨2310093932596253433709987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3080125243461671244946649 2310093932596253433709987)
                ·
                  refine ⟨3465140898894380150564981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310093932596253433709987 3465140898894380150564981)
                  ·
                    refine ⟨324856959271348139115467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3465140898894380150564981 324856959271348139115467)
                    ·
                      rfl

theorem cell23_1897970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_1897970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897970 prefixEnd_1897970 := by exact prefixLift 1897970
  have htrace : WordTrace (prefixWord ++ tailWord_1897970) baseStart_1897970 baseEnd_1897970 := by
    simpa [prefixWord, tailWord_1897970, baseEnd_1897970] using wordTrace_append hprefix tailTrace_1897970
  have hstable : (prefixWord ++ tailWord_1897970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897970).length < 2 ^ (prefixWord ++ tailWord_1897970).sum := by decide
  have hdescent : baseEnd_1897970 < baseStart_1897970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897996 : List Nat := [2, 2, 1, 2, 5, 11]
def baseStart_1897996 : Nat := 118140960795 + 1897996 * 2 ^ 59
def prefixEnd_1897996 : Nat := 4983230072969 + 3 ^ 40 * 1897996 * 2
def baseEnd_1897996 : Nat := 4010634684407659735067

theorem tailTrace_1897996 : CollatzResearch.WordTrace tailWord_1897996 prefixEnd_1897996 4010634684407659735067 := by
  unfold tailWord_1897996
  simp only [CollatzResearch.WordTrace]
  refine ⟨34612800615946059377428921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46150400821261412503238561 34612800615946059377428921)
  ·
    refine ⟨25959600461959544533071691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34612800615946059377428921 25959600461959544533071691)
    ·
      refine ⟨38939400692939316799607537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25959600461959544533071691 38939400692939316799607537)
      ·
        refine ⟨29204550519704487599705653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38939400692939316799607537 29204550519704487599705653)
        ·
          refine ⟨2737926611222295712472405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29204550519704487599705653 2737926611222295712472405)
          ·
            refine ⟨4010634684407659735067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2737926611222295712472405 4010634684407659735067)
            ·
              rfl

theorem cell23_1897996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 11].length) (baseStart_1897996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897996 prefixEnd_1897996 := by exact prefixLift 1897996
  have htrace : WordTrace (prefixWord ++ tailWord_1897996) baseStart_1897996 baseEnd_1897996 := by
    simpa [prefixWord, tailWord_1897996, baseEnd_1897996] using wordTrace_append hprefix tailTrace_1897996
  have hstable : (prefixWord ++ tailWord_1897996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897996).length < 2 ^ (prefixWord ++ tailWord_1897996).sum := by decide
  have hdescent : baseEnd_1897996 < baseStart_1897996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898024 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1898024 : Nat := 118140960795 + 1898024 * 2 ^ 59
def prefixEnd_1898024 : Nat := 4983230072969 + 3 ^ 40 * 1898024 * 2
def baseEnd_1898024 : Nat := 974598605769387206071153

theorem tailTrace_1898024 : CollatzResearch.WordTrace tailWord_1898024 prefixEnd_1898024 974598605769387206071153 := by
  unfold tailWord_1898024
  simp only [CollatzResearch.WordTrace]
  refine ⟨34613311237895339768438563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46151081650527119691251417 34613311237895339768438563)
  ·
    refine ⟨51919966856843009652657845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34613311237895339768438563 51919966856843009652657845)
    ·
      refine ⟨4867496892829032154936673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51919966856843009652657845 4867496892829032154936673)
      ·
        refine ⟨3650622669621774116202505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4867496892829032154936673 3650622669621774116202505)
        ·
          refine ⟨2737967002216330587151879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650622669621774116202505 2737967002216330587151879)
          ·
            refine ⟨4106950503324495880727819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737967002216330587151879 4106950503324495880727819)
            ·
              refine ⟨6160425754986743821091729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106950503324495880727819 6160425754986743821091729)
              ·
                refine ⟨4620319316240057865818797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160425754986743821091729 4620319316240057865818797)
                ·
                  refine ⟨1732619743590021699682049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4620319316240057865818797 1732619743590021699682049)
                  ·
                    refine ⟨1299464807692516274761537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1732619743590021699682049 1299464807692516274761537)
                    ·
                      refine ⟨974598605769387206071153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299464807692516274761537 974598605769387206071153)
                      ·
                        rfl

theorem cell23_1898024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1898024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898024 prefixEnd_1898024 := by exact prefixLift 1898024
  have htrace : WordTrace (prefixWord ++ tailWord_1898024) baseStart_1898024 baseEnd_1898024 := by
    simpa [prefixWord, tailWord_1898024, baseEnd_1898024] using wordTrace_append hprefix tailTrace_1898024
  have hstable : (prefixWord ++ tailWord_1898024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898024).length < 2 ^ (prefixWord ++ tailWord_1898024).sum := by decide
  have hdescent : baseEnd_1898024 < baseStart_1898024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898030 : List Nat := [4, 1, 3, 1, 2, 2, 3, 7]
def baseStart_1898030 : Nat := 118140960795 + 1898030 * 2 ^ 59
def prefixEnd_1898030 : Nat := 4983230072969 + 3 ^ 40 * 1898030 * 2
def baseEnd_1898030 : Nat := 36096358764937562318375

theorem tailTrace_1898030 : CollatzResearch.WordTrace tailWord_1898030 prefixEnd_1898030 36096358764937562318375 := by
  unfold tailWord_1898030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653355164221117820199443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46151227542512628374397029 8653355164221117820199443)
  ·
    refine ⟨12980032746331676730299165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8653355164221117820199443 12980032746331676730299165)
    ·
      refine ⟨4867512279874378773862187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12980032746331676730299165 4867512279874378773862187)
      ·
        refine ⟨7301268419811568160793281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867512279874378773862187 7301268419811568160793281)
        ·
          refine ⟨5475951314858676120594961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7301268419811568160793281 5475951314858676120594961)
          ·
            refine ⟨4106963486144007090446221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475951314858676120594961 4106963486144007090446221)
            ·
              refine ⟨1540111307304002658917333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4106963486144007090446221 1540111307304002658917333)
              ·
                refine ⟨36096358764937562318375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1540111307304002658917333 36096358764937562318375)
                ·
                  rfl

theorem cell23_1898030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_1898030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898030 prefixEnd_1898030 := by exact prefixLift 1898030
  have htrace : WordTrace (prefixWord ++ tailWord_1898030) baseStart_1898030 baseEnd_1898030 := by
    simpa [prefixWord, tailWord_1898030, baseEnd_1898030] using wordTrace_append hprefix tailTrace_1898030
  have hstable : (prefixWord ++ tailWord_1898030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898030).length < 2 ^ (prefixWord ++ tailWord_1898030).sum := by decide
  have hdescent : baseEnd_1898030 < baseStart_1898030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898044 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_1898044 : Nat := 118140960795 + 1898044 * 2 ^ 59
def prefixEnd_1898044 : Nat := 4983230072969 + 3 ^ 40 * 1898044 * 2
def baseEnd_1898044 : Nat := 974608875382477127821061

theorem tailTrace_1898044 : CollatzResearch.WordTrace tailWord_1898044 prefixEnd_1898044 974608875382477127821061 := by
  unfold tailWord_1898044
  simp only [CollatzResearch.WordTrace]
  refine ⟨34613675967859111476302593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46151567957145481968403457 34613675967859111476302593)
  ·
    refine ⟨25960256975894333607226945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34613675967859111476302593 25960256975894333607226945)
    ·
      refine ⟨19470192731920750205420209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25960256975894333607226945 19470192731920750205420209)
      ·
        refine ⟨14602644548940562654065157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19470192731920750205420209 14602644548940562654065157)
        ·
          refine ⟨2737995852926355497637217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14602644548940562654065157 2737995852926355497637217)
          ·
            refine ⟨2053496889694766623227913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2737995852926355497637217 2053496889694766623227913)
            ·
              refine ⟨1540122667271074967420935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053496889694766623227913 1540122667271074967420935)
              ·
                refine ⟨2310184000906612451131403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540122667271074967420935 2310184000906612451131403)
                ·
                  refine ⟨3465276001359918676697105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310184000906612451131403 3465276001359918676697105)
                  ·
                    refine ⟨2598957001019939007522829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3465276001359918676697105 2598957001019939007522829)
                    ·
                      refine ⟨974608875382477127821061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2598957001019939007522829 974608875382477127821061)
                      ·
                        rfl

theorem cell23_1898044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_1898044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898044 prefixEnd_1898044 := by exact prefixLift 1898044
  have htrace : WordTrace (prefixWord ++ tailWord_1898044) baseStart_1898044 baseEnd_1898044 := by
    simpa [prefixWord, tailWord_1898044, baseEnd_1898044] using wordTrace_append hprefix tailTrace_1898044
  have hstable : (prefixWord ++ tailWord_1898044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898044).length < 2 ^ (prefixWord ++ tailWord_1898044).sum := by decide
  have hdescent : baseEnd_1898044 < baseStart_1898044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898170 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1898170 : Nat := 118140960795 + 1898170 * 2 ^ 59
def prefixEnd_1898170 : Nat := 4983230072969 + 3 ^ 40 * 1898170 * 2
def baseEnd_1898170 : Nat := 974673573944943634845481

theorem tailTrace_1898170 : CollatzResearch.WordTrace tailWord_1898170 prefixEnd_1898170 974673573944943634845481 := by
  unfold tailWord_1898170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307986883315436617922991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46154631688841164314461309 17307986883315436617922991)
  ·
    refine ⟨25961980324973154926884487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17307986883315436617922991 25961980324973154926884487)
    ·
      refine ⟨38942970487459732390326731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25961980324973154926884487 38942970487459732390326731)
      ·
        refine ⟨58414455731189598585490097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38942970487459732390326731 58414455731189598585490097)
        ·
          refine ⟨43810841798392198939117573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58414455731189598585490097 43810841798392198939117573)
          ·
            refine ⟨8214532837198537301084545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43810841798392198939117573 8214532837198537301084545)
            ·
              refine ⟨6160899627898902975813409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8214532837198537301084545 6160899627898902975813409)
              ·
                refine ⟨4620674720924177231860057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160899627898902975813409 4620674720924177231860057)
                ·
                  refine ⟨3465506040693132923895043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4620674720924177231860057 3465506040693132923895043)
                  ·
                    refine ⟨5198259061039699385842565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3465506040693132923895043 5198259061039699385842565)
                    ·
                      refine ⟨974673573944943634845481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5198259061039699385842565 974673573944943634845481)
                      ·
                        rfl

theorem cell23_1898170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1898170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898170 prefixEnd_1898170 := by exact prefixLift 1898170
  have htrace : WordTrace (prefixWord ++ tailWord_1898170) baseStart_1898170 baseEnd_1898170 := by
    simpa [prefixWord, tailWord_1898170, baseEnd_1898170] using wordTrace_append hprefix tailTrace_1898170
  have hstable : (prefixWord ++ tailWord_1898170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898170).length < 2 ^ (prefixWord ++ tailWord_1898170).sum := by decide
  have hdescent : baseEnd_1898170 < baseStart_1898170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898173 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1898173 : Nat := 118140960795 + 1898173 * 2 ^ 59
def prefixEnd_1898173 : Nat := 4983230072969 + 3 ^ 40 * 1898173 * 2
def baseEnd_1898173 : Nat := 974675114386907123107967

theorem tailTrace_1898173 : CollatzResearch.WordTrace tailWord_1898173 prefixEnd_1898173 974675114386907123107967 := by
  unfold tailWord_1898173
  simp only [CollatzResearch.WordTrace]
  refine ⟨69232056952250877984051173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46154704634833918656034115 69232056952250877984051173)
  ·
    refine ⟨12981010678547039622009595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69232056952250877984051173 12981010678547039622009595)
    ·
      refine ⟨19471516017820559433014393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981010678547039622009595 19471516017820559433014393)
      ·
        refine ⟨14603637013365419574760795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19471516017820559433014393 14603637013365419574760795)
        ·
          refine ⟨21905455520048129362141193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14603637013365419574760795 21905455520048129362141193)
          ·
            refine ⟨16429091640036097021605895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21905455520048129362141193 16429091640036097021605895)
            ·
              refine ⟨24643637460054145532408843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16429091640036097021605895 24643637460054145532408843)
              ·
                refine ⟨36965456190081218298613265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24643637460054145532408843 36965456190081218298613265)
                ·
                  refine ⟨27724092142560913723959949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36965456190081218298613265 27724092142560913723959949)
                  ·
                    refine ⟨10396534553460342646484981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27724092142560913723959949 10396534553460342646484981)
                    ·
                      refine ⟨974675114386907123107967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10396534553460342646484981 974675114386907123107967)
                      ·
                        rfl

theorem cell23_1898173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1898173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898173 prefixEnd_1898173 := by exact prefixLift 1898173
  have htrace : WordTrace (prefixWord ++ tailWord_1898173) baseStart_1898173 baseEnd_1898173 := by
    simpa [prefixWord, tailWord_1898173, baseEnd_1898173] using wordTrace_append hprefix tailTrace_1898173
  have hstable : (prefixWord ++ tailWord_1898173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898173).length < 2 ^ (prefixWord ++ tailWord_1898173).sum := by decide
  have hdescent : baseEnd_1898173 < baseStart_1898173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898190 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1898190 : Nat := 118140960795 + 1898190 * 2 ^ 59
def prefixEnd_1898190 : Nat := 4983230072969 + 3 ^ 40 * 1898190 * 2
def baseEnd_1898190 : Nat := 974683843558033556595389

theorem tailTrace_1898190 : CollatzResearch.WordTrace tailWord_1898190 prefixEnd_1898190 974683843558033556595389 := by
  unfold tailWord_1898190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654084624148661235927503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46155117995459526591613349 8654084624148661235927503)
  ·
    refine ⟨12981126936222991853891255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654084624148661235927503 12981126936222991853891255)
    ·
      refine ⟨19471690404334487780836883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981126936222991853891255 19471690404334487780836883)
      ·
        refine ⟨29207535606501731671255325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19471690404334487780836883 29207535606501731671255325)
        ·
          refine ⟨10952825852438149376720747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29207535606501731671255325 10952825852438149376720747)
          ·
            refine ⟨16429238778657224065081121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10952825852438149376720747 16429238778657224065081121)
            ·
              refine ⟨12321929083992918048810841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16429238778657224065081121 12321929083992918048810841)
              ·
                refine ⟨9241446812994688536608131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12321929083992918048810841 9241446812994688536608131)
                ·
                  refine ⟨13862170219492032804912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241446812994688536608131 13862170219492032804912197)
                  ·
                    refine ⟨2599156916154756150921037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13862170219492032804912197 2599156916154756150921037)
                    ·
                      refine ⟨974683843558033556595389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2599156916154756150921037 974683843558033556595389)
                      ·
                        rfl

theorem cell23_1898190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1898190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898190 prefixEnd_1898190 := by exact prefixLift 1898190
  have htrace : WordTrace (prefixWord ++ tailWord_1898190) baseStart_1898190 baseEnd_1898190 := by
    simpa [prefixWord, tailWord_1898190, baseEnd_1898190] using wordTrace_append hprefix tailTrace_1898190
  have hstable : (prefixWord ++ tailWord_1898190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898190).length < 2 ^ (prefixWord ++ tailWord_1898190).sum := by decide
  have hdescent : baseEnd_1898190 < baseStart_1898190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898230 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1898230 : Nat := 118140960795 + 1898230 * 2 ^ 59
def prefixEnd_1898230 : Nat := 4983230072969 + 3 ^ 40 * 1898230 * 2
def baseEnd_1898230 : Nat := 974704382784213400095205

theorem tailTrace_1898230 : CollatzResearch.WordTrace tailWord_1898230 prefixEnd_1898230 974704382784213400095205 := by
  unfold tailWord_1898230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327133494565273544929759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46156090608696251145917429 4327133494565273544929759)
  ·
    refine ⟨6490700241847910317394639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4327133494565273544929759 6490700241847910317394639)
    ·
      refine ⟨9736050362771865476091959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490700241847910317394639 9736050362771865476091959)
      ·
        refine ⟨14604075544157798214137939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736050362771865476091959 14604075544157798214137939)
        ·
          refine ⟨21906113316236697321206909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14604075544157798214137939 21906113316236697321206909)
          ·
            refine ⟨8214792493588761495452591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21906113316236697321206909 8214792493588761495452591)
            ·
              refine ⟨12322188740383142243178887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214792493588761495452591 12322188740383142243178887)
              ·
                refine ⟨18483283110574713364768331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12322188740383142243178887 18483283110574713364768331)
                ·
                  refine ⟨27724924665862070047152497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18483283110574713364768331 27724924665862070047152497)
                  ·
                    refine ⟨20793693499396552535364373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27724924665862070047152497 20793693499396552535364373)
                    ·
                      refine ⟨974704382784213400095205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20793693499396552535364373 974704382784213400095205)
                      ·
                        rfl

theorem cell23_1898230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1898230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898230 prefixEnd_1898230 := by exact prefixLift 1898230
  have htrace : WordTrace (prefixWord ++ tailWord_1898230) baseStart_1898230 baseEnd_1898230 := by
    simpa [prefixWord, tailWord_1898230, baseEnd_1898230] using wordTrace_append hprefix tailTrace_1898230
  have hstable : (prefixWord ++ tailWord_1898230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898230).length < 2 ^ (prefixWord ++ tailWord_1898230).sum := by decide
  have hdescent : baseEnd_1898230 < baseStart_1898230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898277 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_1898277 : Nat := 118140960795 + 1898277 * 2 ^ 59
def prefixEnd_1898277 : Nat := 4983230072969 + 3 ^ 40 * 1898277 * 2
def baseEnd_1898277 : Nat := 974728516374974716207489

theorem tailTrace_1898277 : CollatzResearch.WordTrace tailWord_1898277 prefixEnd_1898277 974728516374974716207489 := by
  unfold tailWord_1898277
  simp only [CollatzResearch.WordTrace]
  refine ⟨69235850143874103745837085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46157233429249402497224723 69235850143874103745837085)
  ·
    refine ⟨25963443803952788904688907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69235850143874103745837085 25963443803952788904688907)
    ·
      refine ⟨38945165705929183357033361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25963443803952788904688907 38945165705929183357033361)
      ·
        refine ⟨29208874279446887517775021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38945165705929183357033361 29208874279446887517775021)
        ·
          refine ⟨10953327854792582819165633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29208874279446887517775021 10953327854792582819165633)
          ·
            refine ⟨8214995891094437114374225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10953327854792582819165633 8214995891094437114374225)
            ·
              refine ⟨6161246918320827835780669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8214995891094437114374225 6161246918320827835780669)
              ·
                refine ⟨2310467594370310438417751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6161246918320827835780669 2310467594370310438417751)
                ·
                  refine ⟨3465701391555465657626627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310467594370310438417751 3465701391555465657626627)
                  ·
                    refine ⟨5198552087333198486439941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3465701391555465657626627 5198552087333198486439941)
                    ·
                      refine ⟨974728516374974716207489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5198552087333198486439941 974728516374974716207489)
                      ·
                        rfl

theorem cell23_1898277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_1898277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898277 prefixEnd_1898277 := by exact prefixLift 1898277
  have htrace : WordTrace (prefixWord ++ tailWord_1898277) baseStart_1898277 baseEnd_1898277 := by
    simpa [prefixWord, tailWord_1898277, baseEnd_1898277] using wordTrace_append hprefix tailTrace_1898277
  have hstable : (prefixWord ++ tailWord_1898277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898277).length < 2 ^ (prefixWord ++ tailWord_1898277).sum := by decide
  have hdescent : baseEnd_1898277 < baseStart_1898277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898290 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1898290 : Nat := 118140960795 + 1898290 * 2 ^ 59
def prefixEnd_1898290 : Nat := 4983230072969 + 3 ^ 40 * 1898290 * 2
def baseEnd_1898290 : Nat := 974735191623483165344929

theorem tailTrace_1898290 : CollatzResearch.WordTrace tailWord_1898290 prefixEnd_1898290 974735191623483165344929 := by
  unfold tailWord_1898290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309081073206751741515081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46157549528551337977373549 17309081073206751741515081)
  ·
    refine ⟨12981810804905063806136311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17309081073206751741515081 12981810804905063806136311)
    ·
      refine ⟨19472716207357595709204467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12981810804905063806136311 19472716207357595709204467)
      ·
        refine ⟨29209074311036393563806701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19472716207357595709204467 29209074311036393563806701)
        ·
          refine ⟨10953402866638647586427513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29209074311036393563806701 10953402866638647586427513)
          ·
            refine ⟨8215052149978985689820635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10953402866638647586427513 8215052149978985689820635)
            ·
              refine ⟨12322578224968478534730953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215052149978985689820635 12322578224968478534730953)
              ·
                refine ⟨9241933668726358901048215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12322578224968478534730953 9241933668726358901048215)
                ·
                  refine ⟨13862900503089538351572323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241933668726358901048215 13862900503089538351572323)
                  ·
                    refine ⟨20794350754634307527358485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13862900503089538351572323 20794350754634307527358485)
                    ·
                      refine ⟨974735191623483165344929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20794350754634307527358485 974735191623483165344929)
                      ·
                        rfl

theorem cell23_1898290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1898290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898290 prefixEnd_1898290 := by exact prefixLift 1898290
  have htrace : WordTrace (prefixWord ++ tailWord_1898290) baseStart_1898290 baseEnd_1898290 := by
    simpa [prefixWord, tailWord_1898290, baseEnd_1898290] using wordTrace_append hprefix tailTrace_1898290
  have hstable : (prefixWord ++ tailWord_1898290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898290).length < 2 ^ (prefixWord ++ tailWord_1898290).sum := by decide
  have hdescent : baseEnd_1898290 < baseStart_1898290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898317 : List Nat := [1, 6, 1, 2, 1, 1, 2, 9]
def baseStart_1898317 : Nat := 118140960795 + 1898317 * 2 ^ 59
def prefixEnd_1898317 : Nat := 4983230072969 + 3 ^ 40 * 1898317 * 2
def baseEnd_1898317 : Nat := 36101816874116835544715

theorem tailTrace_1898317 : CollatzResearch.WordTrace tailWord_1898317 prefixEnd_1898317 36101816874116835544715 := by
  unfold tailWord_1898317
  simp only [CollatzResearch.WordTrace]
  refine ⟨69237309063729190577293205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46158206042486127051528803 69237309063729190577293205)
  ·
    refine ⟨3245498862362305808310619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69237309063729190577293205 3245498862362305808310619)
    ·
      refine ⟨4868248293543458712465929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245498862362305808310619 4868248293543458712465929)
      ·
        refine ⟨3651186220157594034349447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4868248293543458712465929 3651186220157594034349447)
        ·
          refine ⟨5476779330236391051524171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651186220157594034349447 5476779330236391051524171)
          ·
            refine ⟨8215168995354586577286257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476779330236391051524171 8215168995354586577286257)
            ·
              refine ⟨6161376746515939932964693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8215168995354586577286257 6161376746515939932964693)
              ·
                refine ⟨36101816874116835544715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6161376746515939932964693 36101816874116835544715)
                ·
                  rfl

theorem cell23_1898317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 9].length) (baseStart_1898317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898317 prefixEnd_1898317 := by exact prefixLift 1898317
  have htrace : WordTrace (prefixWord ++ tailWord_1898317) baseStart_1898317 baseEnd_1898317 := by
    simpa [prefixWord, tailWord_1898317, baseEnd_1898317] using wordTrace_append hprefix tailTrace_1898317
  have hstable : (prefixWord ++ tailWord_1898317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898317).length < 2 ^ (prefixWord ++ tailWord_1898317).sum := by decide
  have hdescent : baseEnd_1898317 < baseStart_1898317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898380 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1898380 : Nat := 118140960795 + 1898380 * 2 ^ 59
def prefixEnd_1898380 : Nat := 4983230072969 + 3 ^ 40 * 1898380 * 2
def baseEnd_1898380 : Nat := 974781404882387813219515

theorem tailTrace_1898380 : CollatzResearch.WordTrace tailWord_1898380 prefixEnd_1898380 974781404882387813219515 := by
  unfold tailWord_1898380
  simp only [CollatzResearch.WordTrace]
  refine ⟨34619803431250476168418297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46159737908333968224557729 34619803431250476168418297)
  ·
    refine ⟨25964852573437857126313723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34619803431250476168418297 25964852573437857126313723)
    ·
      refine ⟨38947278860156785689470585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25964852573437857126313723 38947278860156785689470585)
      ·
        refine ⟨29210459145117589267102939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38947278860156785689470585 29210459145117589267102939)
        ·
          refine ⟨43815688717676383900654409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29210459145117589267102939 43815688717676383900654409)
          ·
            refine ⟨32861766538257287925490807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43815688717676383900654409 32861766538257287925490807)
            ·
              refine ⟨49292649807385931888236211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32861766538257287925490807 49292649807385931888236211)
              ·
                refine ⟨73938974711078897832354317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49292649807385931888236211 73938974711078897832354317)
                ·
                  refine ⟨27727115516654586687132869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73938974711078897832354317 27727115516654586687132869)
                  ·
                    refine ⟨5198834159372735003837413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27727115516654586687132869 5198834159372735003837413)
                    ·
                      refine ⟨974781404882387813219515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5198834159372735003837413 974781404882387813219515)
                      ·
                        rfl

theorem cell23_1898380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1898380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898380 prefixEnd_1898380 := by exact prefixLift 1898380
  have htrace : WordTrace (prefixWord ++ tailWord_1898380) baseStart_1898380 baseEnd_1898380 := by
    simpa [prefixWord, tailWord_1898380, baseEnd_1898380] using wordTrace_append hprefix tailTrace_1898380
  have hstable : (prefixWord ++ tailWord_1898380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898380).length < 2 ^ (prefixWord ++ tailWord_1898380).sum := by decide
  have hdescent : baseEnd_1898380 < baseStart_1898380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898388 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1898388 : Nat := 118140960795 + 1898388 * 2 ^ 59
def prefixEnd_1898388 : Nat := 4983230072969 + 3 ^ 40 * 1898388 * 2
def baseEnd_1898388 : Nat := 974785512727623781919479

theorem tailTrace_1898388 : CollatzResearch.WordTrace tailWord_1898388 prefixEnd_1898388 974785512727623781919479 := by
  unfold tailWord_1898388
  simp only [CollatzResearch.WordTrace]
  refine ⟨34619949323235984851563909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46159932430981313135418545 34619949323235984851563909)
  ·
    refine ⟨6491240498106747159668233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34619949323235984851563909 6491240498106747159668233)
    ·
      refine ⟨4868430373580060369751175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6491240498106747159668233 4868430373580060369751175)
      ·
        refine ⟨7302645560370090554626763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868430373580060369751175 7302645560370090554626763)
        ·
          refine ⟨10953968340555135831940145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7302645560370090554626763 10953968340555135831940145)
          ·
            refine ⟨8215476255416351873955109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10953968340555135831940145 8215476255416351873955109)
            ·
              refine ⟨1540401797890565976366583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8215476255416351873955109 1540401797890565976366583)
              ·
                refine ⟨2310602696835848964549875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540401797890565976366583 2310602696835848964549875)
                ·
                  refine ⟨3465904045253773446824813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310602696835848964549875 3465904045253773446824813)
                  ·
                    refine ⟨1299714016970165042559305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465904045253773446824813 1299714016970165042559305)
                    ·
                      refine ⟨974785512727623781919479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299714016970165042559305 974785512727623781919479)
                      ·
                        rfl

theorem cell23_1898388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1898388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898388 prefixEnd_1898388 := by exact prefixLift 1898388
  have htrace : WordTrace (prefixWord ++ tailWord_1898388) baseStart_1898388 baseEnd_1898388 := by
    simpa [prefixWord, tailWord_1898388, baseEnd_1898388] using wordTrace_append hprefix tailTrace_1898388
  have hstable : (prefixWord ++ tailWord_1898388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898388).length < 2 ^ (prefixWord ++ tailWord_1898388).sum := by decide
  have hdescent : baseEnd_1898388 < baseStart_1898388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898397 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1898397 : Nat := 118140960795 + 1898397 * 2 ^ 59
def prefixEnd_1898397 : Nat := 4983230072969 + 3 ^ 40 * 1898397 * 2
def baseEnd_1898397 : Nat := 974790134053514246706937

theorem tailTrace_1898397 : CollatzResearch.WordTrace tailWord_1898397 prefixEnd_1898397 974790134053514246706937 := by
  unfold tailWord_1898397
  simp only [CollatzResearch.WordTrace]
  refine ⟨69240226903439364240205445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46160151268959576160136963 69240226903439364240205445)
  ·
    refine ⟨12982542544394880795038521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69240226903439364240205445 12982542544394880795038521)
    ·
      refine ⟨9736906908296160596278891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12982542544394880795038521 9736906908296160596278891)
      ·
        refine ⟨14605360362444240894418337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9736906908296160596278891 14605360362444240894418337)
        ·
          refine ⟨10954020271833180670813753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14605360362444240894418337 10954020271833180670813753)
          ·
            refine ⟨8215515203874885503110315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10954020271833180670813753 8215515203874885503110315)
            ·
              refine ⟨12323272805812328254665473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215515203874885503110315 12323272805812328254665473)
              ·
                refine ⟨9242454604359246190999105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12323272805812328254665473 9242454604359246190999105)
                ·
                  refine ⟨6931840953269434643249329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242454604359246190999105 6931840953269434643249329)
                  ·
                    refine ⟨5198880714952075982436997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6931840953269434643249329 5198880714952075982436997)
                    ·
                      refine ⟨974790134053514246706937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5198880714952075982436997 974790134053514246706937)
                      ·
                        rfl

theorem cell23_1898397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1898397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898397 prefixEnd_1898397 := by exact prefixLift 1898397
  have htrace : WordTrace (prefixWord ++ tailWord_1898397) baseStart_1898397 baseEnd_1898397 := by
    simpa [prefixWord, tailWord_1898397, baseEnd_1898397] using wordTrace_append hprefix tailTrace_1898397
  have hstable : (prefixWord ++ tailWord_1898397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898397).length < 2 ^ (prefixWord ++ tailWord_1898397).sum := by decide
  have hdescent : baseEnd_1898397 < baseStart_1898397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898407 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 7]
def baseStart_1898407 : Nat := 118140960795 + 1898407 * 2 ^ 59
def prefixEnd_1898407 : Nat := 4983230072969 + 3 ^ 40 * 1898407 * 2
def baseEnd_1898407 : Nat := 108310585428895467509099

theorem tailTrace_1898407 : CollatzResearch.WordTrace tailWord_1898407 prefixEnd_1898407 108310585428895467509099 := by
  unfold tailWord_1898407
  simp only [CollatzResearch.WordTrace]
  refine ⟨69240591633403135948069475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46160394422268757298712983 69240591633403135948069475)
  ·
    refine ⟨103860887450104703922104213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69240591633403135948069475 103860887450104703922104213)
    ·
      refine ⟨4868479099223657996348635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103860887450104703922104213 4868479099223657996348635)
      ·
        refine ⟨7302718648835486994522953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868479099223657996348635 7302718648835486994522953)
        ·
          refine ⟨5477038986626615245892215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7302718648835486994522953 5477038986626615245892215)
          ·
            refine ⟨8215558479939922868838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477038986626615245892215 8215558479939922868838323)
            ·
              refine ⟨12323337719909884303257485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8215558479939922868838323 12323337719909884303257485)
              ·
                refine ⟨4621251644966206613721557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12323337719909884303257485 4621251644966206613721557)
                ·
                  refine ⟨108310585428895467509099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4621251644966206613721557 108310585428895467509099)
                  ·
                    rfl

theorem cell23_1898407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 7].length) (baseStart_1898407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898407 prefixEnd_1898407 := by exact prefixLift 1898407
  have htrace : WordTrace (prefixWord ++ tailWord_1898407) baseStart_1898407 baseEnd_1898407 := by
    simpa [prefixWord, tailWord_1898407, baseEnd_1898407] using wordTrace_append hprefix tailTrace_1898407
  have hstable : (prefixWord ++ tailWord_1898407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898407).length < 2 ^ (prefixWord ++ tailWord_1898407).sum := by decide
  have hdescent : baseEnd_1898407 < baseStart_1898407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898427 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 5, 2]
def baseStart_1898427 : Nat := 118140960795 + 1898427 * 2 ^ 59
def prefixEnd_1898427 : Nat := 4983230072969 + 3 ^ 40 * 1898427 * 2
def baseEnd_1898427 : Nat := 974805538473149129331799

theorem tailTrace_1898427 : CollatzResearch.WordTrace tailWord_1898427 prefixEnd_1898427 974805538473149129331799 := by
  unfold tailWord_1898427
  simp only [CollatzResearch.WordTrace]
  refine ⟨69241321093330679363797535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46160880728887119575865023 69241321093330679363797535)
  ·
    refine ⟨103861981639996019045696303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69241321093330679363797535 103861981639996019045696303)
    ·
      refine ⟨155792972459994028568544455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103861981639996019045696303 155792972459994028568544455)
      ·
        refine ⟨233689458689991042852816683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155792972459994028568544455 233689458689991042852816683)
        ·
          refine ⟨350534188034986564279225025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233689458689991042852816683 350534188034986564279225025)
          ·
            refine ⟨262900641026239923209418769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350534188034986564279225025 262900641026239923209418769)
            ·
              refine ⟨197175480769679942407064077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262900641026239923209418769 197175480769679942407064077)
              ·
                refine ⟨73940805288629978402649029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197175480769679942407064077 73940805288629978402649029)
                ·
                  refine ⟨13863900991618120950496693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73940805288629978402649029 13863900991618120950496693)
                  ·
                    refine ⟨1299740717964198839109065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13863900991618120950496693 1299740717964198839109065)
                    ·
                      refine ⟨974805538473149129331799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299740717964198839109065 974805538473149129331799)
                      ·
                        rfl

theorem cell23_1898427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5, 2].length) (baseStart_1898427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898427 prefixEnd_1898427 := by exact prefixLift 1898427
  have htrace : WordTrace (prefixWord ++ tailWord_1898427) baseStart_1898427 baseEnd_1898427 := by
    simpa [prefixWord, tailWord_1898427, baseEnd_1898427] using wordTrace_append hprefix tailTrace_1898427
  have hstable : (prefixWord ++ tailWord_1898427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898427).length < 2 ^ (prefixWord ++ tailWord_1898427).sum := by decide
  have hdescent : baseEnd_1898427 < baseStart_1898427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898474 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_1898474 : Nat := 118140960795 + 1898474 * 2 ^ 59
def prefixEnd_1898474 : Nat := 4983230072969 + 3 ^ 40 * 1898474 * 2
def baseEnd_1898474 : Nat := 974829672063910445444083

theorem tailTrace_1898474 : CollatzResearch.WordTrace tailWord_1898474 prefixEnd_1898474 974829672063910445444083 := by
  unfold tailWord_1898474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17310758831040101597689619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46162023549440270927172317 17310758831040101597689619)
  ·
    refine ⟨25966138246560152396534429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17310758831040101597689619 25966138246560152396534429)
    ·
      refine ⟨9737301842460057148700411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25966138246560152396534429 9737301842460057148700411)
      ·
        refine ⟨14605952763690085723050617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9737301842460057148700411 14605952763690085723050617)
        ·
          refine ⟨10954464572767564292287963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14605952763690085723050617 10954464572767564292287963)
          ·
            refine ⟨16431696859151346438431945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10954464572767564292287963 16431696859151346438431945)
            ·
              refine ⟨12323772644363509828823959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16431696859151346438431945 12323772644363509828823959)
              ·
                refine ⟨18485658966545264743235939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12323772644363509828823959 18485658966545264743235939)
                ·
                  refine ⟨27728488449817897114853909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18485658966545264743235939 27728488449817897114853909)
                  ·
                    refine ⟨1299772896085213927258777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27728488449817897114853909 1299772896085213927258777)
                    ·
                      refine ⟨974829672063910445444083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299772896085213927258777 974829672063910445444083)
                      ·
                        rfl

theorem cell23_1898474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_1898474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898474 prefixEnd_1898474 := by exact prefixLift 1898474
  have htrace : WordTrace (prefixWord ++ tailWord_1898474) baseStart_1898474 baseEnd_1898474 := by
    simpa [prefixWord, tailWord_1898474, baseEnd_1898474] using wordTrace_append hprefix tailTrace_1898474
  have hstable : (prefixWord ++ tailWord_1898474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898474).length < 2 ^ (prefixWord ++ tailWord_1898474).sum := by decide
  have hdescent : baseEnd_1898474 < baseStart_1898474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898509 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1898509 : Nat := 118140960795 + 1898509 * 2 ^ 59
def prefixEnd_1898509 : Nat := 4983230072969 + 3 ^ 40 * 1898509 * 2
def baseEnd_1898509 : Nat := 108316404876313089834047

theorem tailTrace_1898509 : CollatzResearch.WordTrace tailWord_1898509 prefixEnd_1898509 108316404876313089834047 := by
  unfold tailWord_1898509
  simp only [CollatzResearch.WordTrace]
  refine ⟨69244311879033607368282581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46162874586022404912188387 69244311879033607368282581)
  ·
    refine ⟨1622913559664850172694123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69244311879033607368282581 1622913559664850172694123)
    ·
      refine ⟨2434370339497275259041185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622913559664850172694123 2434370339497275259041185)
      ·
        refine ⟨1825777754622956444280889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434370339497275259041185 1825777754622956444280889)
        ·
          refine ⟨1369333315967217333210667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825777754622956444280889 1369333315967217333210667)
          ·
            refine ⟨2053999973950825999816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369333315967217333210667 2053999973950825999816001)
            ·
              refine ⟨1540499980463119499862001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053999973950825999816001 1540499980463119499862001)
              ·
                refine ⟨1155374985347339624896501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540499980463119499862001 1155374985347339624896501)
                ·
                  refine ⟨108316404876313089834047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1155374985347339624896501 108316404876313089834047)
                  ·
                    rfl

theorem cell23_1898509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1898509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898509 prefixEnd_1898509 := by exact prefixLift 1898509
  have htrace : WordTrace (prefixWord ++ tailWord_1898509) baseStart_1898509 baseEnd_1898509 := by
    simpa [prefixWord, tailWord_1898509, baseEnd_1898509] using wordTrace_append hprefix tailTrace_1898509
  have hstable : (prefixWord ++ tailWord_1898509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898509).length < 2 ^ (prefixWord ++ tailWord_1898509).sum := by decide
  have hdescent : baseEnd_1898509 < baseStart_1898509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898527 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 5, 5]
def baseStart_1898527 : Nat := 118140960795 + 1898527 * 2 ^ 59
def prefixEnd_1898527 : Nat := 4983230072969 + 3 ^ 40 * 1898527 * 2
def baseEnd_1898527 : Nat := 324952295512866246027113

theorem tailTrace_1898527 : CollatzResearch.WordTrace tailWord_1898527 prefixEnd_1898527 324952295512866246027113 := by
  unfold tailWord_1898527
  simp only [CollatzResearch.WordTrace]
  refine ⟨69244968392968396442437835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46163312261978930961625223 69244968392968396442437835)
  ·
    refine ⟨103867452589452594663656753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69244968392968396442437835 103867452589452594663656753)
    ·
      refine ⟨77900589442089445997742565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103867452589452594663656753 77900589442089445997742565)
      ·
        refine ⟨14606360520391771124576731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77900589442089445997742565 14606360520391771124576731)
        ·
          refine ⟨21909540780587656686865097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14606360520391771124576731 21909540780587656686865097)
          ·
            refine ⟨16432155585440742515148823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21909540780587656686865097 16432155585440742515148823)
            ·
              refine ⟨24648233378161113772723235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16432155585440742515148823 24648233378161113772723235)
              ·
                refine ⟨36972350067241670659084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24648233378161113772723235 36972350067241670659084853)
                ·
                  refine ⟨3466157818803906624289205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36972350067241670659084853 3466157818803906624289205)
                  ·
                    refine ⟨324952295512866246027113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3466157818803906624289205 324952295512866246027113)
                    ·
                      rfl

theorem cell23_1898527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_1898527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898527 prefixEnd_1898527 := by exact prefixLift 1898527
  have htrace : WordTrace (prefixWord ++ tailWord_1898527) baseStart_1898527 baseEnd_1898527 := by
    simpa [prefixWord, tailWord_1898527, baseEnd_1898527] using wordTrace_append hprefix tailTrace_1898527
  have hstable : (prefixWord ++ tailWord_1898527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898527).length < 2 ^ (prefixWord ++ tailWord_1898527).sum := by decide
  have hdescent : baseEnd_1898527 < baseStart_1898527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898551 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_1898551 : Nat := 118140960795 + 1898551 * 2 ^ 59
def prefixEnd_1898551 : Nat := 4983230072969 + 3 ^ 40 * 1898551 * 2
def baseEnd_1898551 : Nat := 974869210074306644181229

theorem tailTrace_1898551 : CollatzResearch.WordTrace tailWord_1898551 prefixEnd_1898551 974869210074306644181229 := by
  unfold tailWord_1898551
  simp only [CollatzResearch.WordTrace]
  refine ⟨69245843744881448541311507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46163895829920965694207671 69245843744881448541311507)
  ·
    refine ⟨103868765617322172811967261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69245843744881448541311507 103868765617322172811967261)
    ·
      refine ⟨38950787106495814804487723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103868765617322172811967261 38950787106495814804487723)
      ·
        refine ⟨58426180659743722206731585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38950787106495814804487723 58426180659743722206731585)
        ·
          refine ⟨43819635494807791655048689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58426180659743722206731585 43819635494807791655048689)
          ·
            refine ⟨32864726621105843741286517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43819635494807791655048689 32864726621105843741286517)
            ·
              refine ⟨3081068120728672850745611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32864726621105843741286517 3081068120728672850745611)
              ·
                refine ⟨4621602181093009276118417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081068120728672850745611 4621602181093009276118417)
                ·
                  refine ⟨3466201635819756957088813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4621602181093009276118417 3466201635819756957088813)
                  ·
                    refine ⟨1299825613432408858908305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466201635819756957088813 1299825613432408858908305)
                    ·
                      refine ⟨974869210074306644181229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299825613432408858908305 974869210074306644181229)
                      ·
                        rfl

theorem cell23_1898551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_1898551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898551 prefixEnd_1898551 := by exact prefixLift 1898551
  have htrace : WordTrace (prefixWord ++ tailWord_1898551) baseStart_1898551 baseEnd_1898551 := by
    simpa [prefixWord, tailWord_1898551, baseEnd_1898551] using wordTrace_append hprefix tailTrace_1898551
  have hstable : (prefixWord ++ tailWord_1898551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898551).length < 2 ^ (prefixWord ++ tailWord_1898551).sum := by decide
  have hdescent : baseEnd_1898551 < baseStart_1898551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898561 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1898561 : Nat := 118140960795 + 1898561 * 2 ^ 59
def prefixEnd_1898561 : Nat := 4983230072969 + 3 ^ 40 * 1898561 * 2
def baseEnd_1898561 : Nat := 324958114960283868352061

theorem tailTrace_1898561 : CollatzResearch.WordTrace tailWord_1898561 prefixEnd_1898561 324958114960283868352061 := by
  unfold tailWord_1898561
  simp only [CollatzResearch.WordTrace]
  refine ⟨69246208474845220249175537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46164138983230146832783691 69246208474845220249175537)
  ·
    refine ⟨51934656356133915186881653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69246208474845220249175537 51934656356133915186881653)
    ·
      refine ⟨4868874033387554548770155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51934656356133915186881653 4868874033387554548770155)
      ·
        refine ⟨7303311050081331823155233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868874033387554548770155 7303311050081331823155233)
        ·
          refine ⟨5477483287560998867366425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7303311050081331823155233 5477483287560998867366425)
          ·
            refine ⟨4108112465670749150524819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477483287560998867366425 4108112465670749150524819)
            ·
              refine ⟨6162168698506123725787229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108112465670749150524819 6162168698506123725787229)
              ·
                refine ⟨2310813261939796397170211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162168698506123725787229 2310813261939796397170211)
                ·
                  refine ⟨3466219892909694595755317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310813261939796397170211 3466219892909694595755317)
                  ·
                    refine ⟨324958114960283868352061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3466219892909694595755317 324958114960283868352061)
                    ·
                      rfl

theorem cell23_1898561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1898561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898561 prefixEnd_1898561 := by exact prefixLift 1898561
  have htrace : WordTrace (prefixWord ++ tailWord_1898561) baseStart_1898561 baseEnd_1898561 := by
    simpa [prefixWord, tailWord_1898561, baseEnd_1898561] using wordTrace_append hprefix tailTrace_1898561
  have hstable : (prefixWord ++ tailWord_1898561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898561).length < 2 ^ (prefixWord ++ tailWord_1898561).sum := by decide
  have hdescent : baseEnd_1898561 < baseStart_1898561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898577 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_1898577 : Nat := 118140960795 + 1898577 * 2 ^ 59
def prefixEnd_1898577 : Nat := 4983230072969 + 3 ^ 40 * 1898577 * 2
def baseEnd_1898577 : Nat := 974882560571323542456109

theorem tailTrace_1898577 : CollatzResearch.WordTrace tailWord_1898577 prefixEnd_1898577 974882560571323542456109 := by
  unfold tailWord_1898577
  simp only [CollatzResearch.WordTrace]
  refine ⟨69246792042787254981757985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46164528028524836654505323 69246792042787254981757985)
  ·
    refine ⟨51935094032090441236318489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69246792042787254981757985 51935094032090441236318489)
    ·
      refine ⟨38951320524067830927238867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51935094032090441236318489 38951320524067830927238867)
      ·
        refine ⟨58426980786101746390858301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38951320524067830927238867 58426980786101746390858301)
        ·
          refine ⟨21910117794788154896571863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58426980786101746390858301 21910117794788154896571863)
          ·
            refine ⟨32865176692182232344857795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21910117794788154896571863 32865176692182232344857795)
            ·
              refine ⟨49297765038273348517286693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32865176692182232344857795 49297765038273348517286693)
              ·
                refine ⟨9243330944676252846991255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49297765038273348517286693 9243330944676252846991255)
                ·
                  refine ⟨13864996417014379270486883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9243330944676252846991255 13864996417014379270486883)
                  ·
                    refine ⟨20797494625521568905730325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13864996417014379270486883 20797494625521568905730325)
                    ·
                      refine ⟨974882560571323542456109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20797494625521568905730325 974882560571323542456109)
                      ·
                        rfl

theorem cell23_1898577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_1898577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898577 prefixEnd_1898577 := by exact prefixLift 1898577
  have htrace : WordTrace (prefixWord ++ tailWord_1898577) baseStart_1898577 baseEnd_1898577 := by
    simpa [prefixWord, tailWord_1898577, baseEnd_1898577] using wordTrace_append hprefix tailTrace_1898577
  have hstable : (prefixWord ++ tailWord_1898577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898577).length < 2 ^ (prefixWord ++ tailWord_1898577).sum := by decide
  have hdescent : baseEnd_1898577 < baseStart_1898577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898584 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1898584 : Nat := 118140960795 + 1898584 * 2 ^ 59
def prefixEnd_1898584 : Nat := 4983230072969 + 3 ^ 40 * 1898584 * 2
def baseEnd_1898584 : Nat := 974886154935905015068577

theorem tailTrace_1898584 : CollatzResearch.WordTrace tailWord_1898584 prefixEnd_1898584 974886154935905015068577 := by
  unfold tailWord_1898584
  simp only [CollatzResearch.WordTrace]
  refine ⟨34623523676880947588631403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46164698235841263451508537 34623523676880947588631403)
  ·
    refine ⟨51935285515321421382947105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34623523676880947588631403 51935285515321421382947105)
    ·
      refine ⟨38951464136491066037210329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51935285515321421382947105 38951464136491066037210329)
      ·
        refine ⟨29213598102368299527907747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38951464136491066037210329 29213598102368299527907747)
        ·
          refine ⟨43820397153552449291861621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213598102368299527907747 43820397153552449291861621)
          ·
            refine ⟨4108162233145542121112027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43820397153552449291861621 4108162233145542121112027)
            ·
              refine ⟨6162243349718313181668041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108162233145542121112027 6162243349718313181668041)
              ·
                refine ⟨4621682512288734886251031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162243349718313181668041 4621682512288734886251031)
                ·
                  refine ⟨6932523768433102329376547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621682512288734886251031 6932523768433102329376547)
                  ·
                    refine ⟨10398785652649653494064821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932523768433102329376547 10398785652649653494064821)
                    ·
                      refine ⟨974886154935905015068577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10398785652649653494064821 974886154935905015068577)
                      ·
                        rfl

theorem cell23_1898584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1898584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898584 prefixEnd_1898584 := by exact prefixLift 1898584
  have htrace : WordTrace (prefixWord ++ tailWord_1898584) baseStart_1898584 baseEnd_1898584 := by
    simpa [prefixWord, tailWord_1898584, baseEnd_1898584] using wordTrace_append hprefix tailTrace_1898584
  have hstable : (prefixWord ++ tailWord_1898584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898584).length < 2 ^ (prefixWord ++ tailWord_1898584).sum := by decide
  have hdescent : baseEnd_1898584 < baseStart_1898584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898601 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_1898601 : Nat := 118140960795 + 1898601 * 2 ^ 59
def prefixEnd_1898601 : Nat := 4983230072969 + 3 ^ 40 * 1898601 * 2
def baseEnd_1898601 : Nat := 974894884107031448555999

theorem tailTrace_1898601 : CollatzResearch.WordTrace tailWord_1898601 prefixEnd_1898601 974894884107031448555999 := by
  unfold tailWord_1898601
  simp only [CollatzResearch.WordTrace]
  refine ⟨69247667394700307080631657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46165111596466871387087771 69247667394700307080631657)
  ·
    refine ⟨51935750546025230310473743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69247667394700307080631657 51935750546025230310473743)
    ·
      refine ⟨77903625819037845465710615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51935750546025230310473743 77903625819037845465710615)
      ·
        refine ⟨116855438728556768198565923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77903625819037845465710615 116855438728556768198565923)
        ·
          refine ⟨175283158092835152297848885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116855438728556768198565923 175283158092835152297848885)
          ·
            refine ⟨16432796071203295527923333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175283158092835152297848885 16432796071203295527923333)
            ·
              refine ⟨3081149263350617911485625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16432796071203295527923333 3081149263350617911485625)
              ·
                refine ⟨2310861947512963433614219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081149263350617911485625 2310861947512963433614219)
                ·
                  refine ⟨3466292921269445150421329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310861947512963433614219 3466292921269445150421329)
                  ·
                    refine ⟨2599719690952083862815997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466292921269445150421329 2599719690952083862815997)
                    ·
                      refine ⟨974894884107031448555999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2599719690952083862815997 974894884107031448555999)
                      ·
                        rfl

theorem cell23_1898601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_1898601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898601 prefixEnd_1898601 := by exact prefixLift 1898601
  have htrace : WordTrace (prefixWord ++ tailWord_1898601) baseStart_1898601 baseEnd_1898601 := by
    simpa [prefixWord, tailWord_1898601, baseEnd_1898601] using wordTrace_append hprefix tailTrace_1898601
  have hstable : (prefixWord ++ tailWord_1898601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898601).length < 2 ^ (prefixWord ++ tailWord_1898601).sum := by decide
  have hdescent : baseEnd_1898601 < baseStart_1898601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898604 : List Nat := [2, 2, 1, 1, 3, 3, 4, 7]
def baseStart_1898604 : Nat := 118140960795 + 1898604 * 2 ^ 59
def prefixEnd_1898604 : Nat := 4983230072969 + 3 ^ 40 * 1898604 * 2
def baseEnd_1898604 : Nat := 36107274983296108771055

theorem tailTrace_1898604 : CollatzResearch.WordTrace tailWord_1898604 prefixEnd_1898604 36107274983296108771055 := by
  unfold tailWord_1898604
  simp only [CollatzResearch.WordTrace]
  refine ⟨34623888406844719296495433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46165184542459625728660577 34623888406844719296495433)
  ·
    refine ⟨25967916305133539472371575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34623888406844719296495433 25967916305133539472371575)
    ·
      refine ⟨38951874457700309208557363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25967916305133539472371575 38951874457700309208557363)
      ·
        refine ⟨58427811686550463812836045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38951874457700309208557363 58427811686550463812836045)
        ·
          refine ⟨21910429382456423929813517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58427811686550463812836045 21910429382456423929813517)
          ·
            refine ⟨8216411018421158973680069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21910429382456423929813517 8216411018421158973680069)
            ·
              refine ⟨1540577065953967307565013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8216411018421158973680069 1540577065953967307565013)
              ·
                refine ⟨36107274983296108771055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1540577065953967307565013 36107274983296108771055)
                ·
                  rfl

theorem cell23_1898604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 7].length) (baseStart_1898604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898604 prefixEnd_1898604 := by exact prefixLift 1898604
  have htrace : WordTrace (prefixWord ++ tailWord_1898604) baseStart_1898604 baseEnd_1898604 := by
    simpa [prefixWord, tailWord_1898604, baseEnd_1898604] using wordTrace_append hprefix tailTrace_1898604
  have hstable : (prefixWord ++ tailWord_1898604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898604).length < 2 ^ (prefixWord ++ tailWord_1898604).sum := by decide
  have hdescent : baseEnd_1898604 < baseStart_1898604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898615 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 1, 2, 2]
def baseStart_1898615 : Nat := 118140960795 + 1898615 * 2 ^ 59
def prefixEnd_1898615 : Nat := 4983230072969 + 3 ^ 40 * 1898615 * 2
def baseEnd_1898615 : Nat := 974902072836194393780935

theorem tailTrace_1898615 : CollatzResearch.WordTrace tailWord_1898615 prefixEnd_1898615 974902072836194393780935 := by
  unfold tailWord_1898615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69248178016649587471641299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46165452011099724981094199 69248178016649587471641299)
  ·
    refine ⟨103872267024974381207461949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69248178016649587471641299 103872267024974381207461949)
    ·
      refine ⟨38952100134365392952798231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103872267024974381207461949 38952100134365392952798231)
      ·
        refine ⟨58428150201548089429197347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38952100134365392952798231 58428150201548089429197347)
        ·
          refine ⟨87642225302322134143796021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58428150201548089429197347 87642225302322134143796021)
          ·
            refine ⟨8216458622092700075980877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87642225302322134143796021 8216458622092700075980877)
            ·
              refine ⟨3081171983284762528492829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8216458622092700075980877 3081171983284762528492829)
              ·
                refine ⟨1155439493731785948184811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081171983284762528492829 1155439493731785948184811)
                ·
                  refine ⟨1733159240597678922277217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155439493731785948184811 1733159240597678922277217)
                  ·
                    refine ⟨1299869430448259191707913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1733159240597678922277217 1299869430448259191707913)
                    ·
                      refine ⟨974902072836194393780935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299869430448259191707913 974902072836194393780935)
                      ·
                        rfl

theorem cell23_1898615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_1898615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898615 prefixEnd_1898615 := by exact prefixLift 1898615
  have htrace : WordTrace (prefixWord ++ tailWord_1898615) baseStart_1898615 baseEnd_1898615 := by
    simpa [prefixWord, tailWord_1898615, baseEnd_1898615] using wordTrace_append hprefix tailTrace_1898615
  have hstable : (prefixWord ++ tailWord_1898615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898615).length < 2 ^ (prefixWord ++ tailWord_1898615).sum := by decide
  have hdescent : baseEnd_1898615 < baseStart_1898615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898631 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1898631 : Nat := 118140960795 + 1898631 * 2 ^ 59
def prefixEnd_1898631 : Nat := 4983230072969 + 3 ^ 40 * 1898631 * 2
def baseEnd_1898631 : Nat := 974910288526666331180861

theorem tailTrace_1898631 : CollatzResearch.WordTrace tailWord_1898631 prefixEnd_1898631 974910288526666331180861 := by
  unfold tailWord_1898631
  simp only [CollatzResearch.WordTrace]
  refine ⟨69248761584591622204223747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46165841056394414802815831 69248761584591622204223747)
  ·
    refine ⟨103873142376887433306335621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69248761584591622204223747 103873142376887433306335621)
    ·
      refine ⟨19476214195666393744937929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103873142376887433306335621 19476214195666393744937929)
      ·
        refine ⟨14607160646749795308703447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19476214195666393744937929 14607160646749795308703447)
        ·
          refine ⟨21910740970124692963055171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14607160646749795308703447 21910740970124692963055171)
          ·
            refine ⟨32866111455187039444582757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21910740970124692963055171 32866111455187039444582757)
            ·
              refine ⟨6162395897847569895859267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32866111455187039444582757 6162395897847569895859267)
              ·
                refine ⟨9243593846771354843788901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162395897847569895859267 9243593846771354843788901)
                ·
                  refine ⟨1733173846269629033210419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9243593846771354843788901 1733173846269629033210419)
                  ·
                    refine ⟨2599760769404443549815629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733173846269629033210419 2599760769404443549815629)
                    ·
                      refine ⟨974910288526666331180861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2599760769404443549815629 974910288526666331180861)
                      ·
                        rfl

theorem cell23_1898631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1898631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898631 prefixEnd_1898631 := by exact prefixLift 1898631
  have htrace : WordTrace (prefixWord ++ tailWord_1898631) baseStart_1898631 baseEnd_1898631 := by
    simpa [prefixWord, tailWord_1898631, baseEnd_1898631] using wordTrace_append hprefix tailTrace_1898631
  have hstable : (prefixWord ++ tailWord_1898631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898631).length < 2 ^ (prefixWord ++ tailWord_1898631).sum := by decide
  have hdescent : baseEnd_1898631 < baseStart_1898631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898646 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1898646 : Nat := 118140960795 + 1898646 * 2 ^ 59
def prefixEnd_1898646 : Nat := 4983230072969 + 3 ^ 40 * 1898646 * 2
def baseEnd_1898646 : Nat := 324972663578827924164431

theorem tailTrace_1898646 : CollatzResearch.WordTrace tailWord_1898646 prefixEnd_1898646 324972663578827924164431 := by
  unfold tailWord_1898646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328081792471079985376237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46166205786358186510679861 4328081792471079985376237)
  ·
    refine ⟨1623030672176654994516089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4328081792471079985376237 1623030672176654994516089)
    ·
      refine ⟨1217273004132491245887067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1623030672176654994516089 1217273004132491245887067)
      ·
        refine ⟨1825909506198736868830601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217273004132491245887067 1825909506198736868830601)
        ·
          refine ⟨1369432129649052651622951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825909506198736868830601 1369432129649052651622951)
          ·
            refine ⟨2054148194473578977434427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369432129649052651622951 2054148194473578977434427)
            ·
              refine ⟨3081222291710368466151641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054148194473578977434427 3081222291710368466151641)
              ·
                refine ⟨2310916718782776349613731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081222291710368466151641 2310916718782776349613731)
                ·
                  refine ⟨3466375078174164524420597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310916718782776349613731 3466375078174164524420597)
                  ·
                    refine ⟨324972663578827924164431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3466375078174164524420597 324972663578827924164431)
                    ·
                      rfl

theorem cell23_1898646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1898646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898646 prefixEnd_1898646 := by exact prefixLift 1898646
  have htrace : WordTrace (prefixWord ++ tailWord_1898646) baseStart_1898646 baseEnd_1898646 := by
    simpa [prefixWord, tailWord_1898646, baseEnd_1898646] using wordTrace_append hprefix tailTrace_1898646
  have hstable : (prefixWord ++ tailWord_1898646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898646).length < 2 ^ (prefixWord ++ tailWord_1898646).sum := by decide
  have hdescent : baseEnd_1898646 < baseStart_1898646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898667 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_1898667 : Nat := 118140960795 + 1898667 * 2 ^ 59
def prefixEnd_1898667 : Nat := 4983230072969 + 3 ^ 40 * 1898667 * 2
def baseEnd_1898667 : Nat := 974928773830228190330695

theorem tailTrace_1898667 : CollatzResearch.WordTrace tailWord_1898667 prefixEnd_1898667 974928773830228190330695 := by
  unfold tailWord_1898667
  simp only [CollatzResearch.WordTrace]
  refine ⟨69250074612461200352534255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46166716408307466901689503 69250074612461200352534255)
  ·
    refine ⟨103875111918691800528801383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69250074612461200352534255 103875111918691800528801383)
    ·
      refine ⟨155812667878037700793202075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103875111918691800528801383 155812667878037700793202075)
      ·
        refine ⟨233719001817056551189803113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155812667878037700793202075 233719001817056551189803113)
        ·
          refine ⟨175289251362792413392352335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233719001817056551189803113 175289251362792413392352335)
          ·
            refine ⟨262933877044188620088528503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175289251362792413392352335 262933877044188620088528503)
            ·
              refine ⟨394400815566282930132792755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262933877044188620088528503 394400815566282930132792755)
              ·
                refine ⟨591601223349424395199189133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394400815566282930132792755 591601223349424395199189133)
                ·
                  refine ⟨221850458756034148199695925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 591601223349424395199189133 221850458756034148199695925)
                  ·
                    refine ⟨20798480508378201393721493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221850458756034148199695925 20798480508378201393721493)
                    ·
                      refine ⟨974928773830228190330695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20798480508378201393721493 974928773830228190330695)
                      ·
                        rfl

theorem cell23_1898667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_1898667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898667 prefixEnd_1898667 := by exact prefixLift 1898667
  have htrace : WordTrace (prefixWord ++ tailWord_1898667) baseStart_1898667 baseEnd_1898667 := by
    simpa [prefixWord, tailWord_1898667, baseEnd_1898667] using wordTrace_append hprefix tailTrace_1898667
  have hstable : (prefixWord ++ tailWord_1898667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898667).length < 2 ^ (prefixWord ++ tailWord_1898667).sum := by decide
  have hdescent : baseEnd_1898667 < baseStart_1898667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898674 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1898674 : Nat := 118140960795 + 1898674 * 2 ^ 59
def prefixEnd_1898674 : Nat := 4983230072969 + 3 ^ 40 * 1898674 * 2
def baseEnd_1898674 : Nat := 974932368194809662943163

theorem tailTrace_1898674 : CollatzResearch.WordTrace tailWord_1898674 prefixEnd_1898674 974932368194809662943163 := by
  unfold tailWord_1898674
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312582480858960137009769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46166886615623893698692717 17312582480858960137009769)
  ·
    refine ⟨12984436860644220102757327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17312582480858960137009769 12984436860644220102757327)
    ·
      refine ⟨19476655290966330154135991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12984436860644220102757327 19476655290966330154135991)
      ·
        refine ⟨29214982936449495231203987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476655290966330154135991 29214982936449495231203987)
        ·
          refine ⟨43822474404674242846805981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29214982936449495231203987 43822474404674242846805981)
          ·
            refine ⟨16433427901752841067552243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43822474404674242846805981 16433427901752841067552243)
            ·
              refine ⟨24650141852629261601328365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433427901752841067552243 24650141852629261601328365)
              ·
                refine ⟨9243803194735973100498137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24650141852629261601328365 9243803194735973100498137)
                ·
                  refine ⟨6932852396051979825373603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9243803194735973100498137 6932852396051979825373603)
                  ·
                    refine ⟨10399278594077969738060405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6932852396051979825373603 10399278594077969738060405)
                    ·
                      refine ⟨974932368194809662943163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10399278594077969738060405 974932368194809662943163)
                      ·
                        rfl

theorem cell23_1898674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1898674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898674 prefixEnd_1898674 := by exact prefixLift 1898674
  have htrace : WordTrace (prefixWord ++ tailWord_1898674) baseStart_1898674 baseEnd_1898674 := by
    simpa [prefixWord, tailWord_1898674, baseEnd_1898674] using wordTrace_append hprefix tailTrace_1898674
  have hstable : (prefixWord ++ tailWord_1898674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898674).length < 2 ^ (prefixWord ++ tailWord_1898674).sum := by decide
  have hdescent : baseEnd_1898674 < baseStart_1898674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898728 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 5]
def baseStart_1898728 : Nat := 118140960795 + 1898728 * 2 ^ 59
def prefixEnd_1898728 : Nat := 4983230072969 + 3 ^ 40 * 1898728 * 2
def baseEnd_1898728 : Nat := 108328899572239161296435

theorem tailTrace_1898728 : CollatzResearch.WordTrace tailWord_1898728 prefixEnd_1898728 108328899572239161296435 := by
  unfold tailWord_1898728
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626149732620103885252419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46168199643493471847003225 34626149732620103885252419)
  ·
    refine ⟨51939224598930155827878629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34626149732620103885252419 51939224598930155827878629)
    ·
      refine ⟨9738604612299404217727243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51939224598930155827878629 9738604612299404217727243)
      ·
        refine ⟨14607906918449106326590865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9738604612299404217727243 14607906918449106326590865)
        ·
          refine ⟨10955930188836829744943149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14607906918449106326590865 10955930188836829744943149)
          ·
            refine ⟨4108473820813811154353681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10955930188836829744943149 4108473820813811154353681)
            ·
              refine ⟨3081355365610358365765261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108473820813811154353681 3081355365610358365765261)
              ·
                refine ⟨1155508262103884387161973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081355365610358365765261 1155508262103884387161973)
                ·
                  refine ⟨108328899572239161296435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1155508262103884387161973 108328899572239161296435)
                  ·
                    rfl

theorem cell23_1898728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 5].length) (baseStart_1898728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898728 prefixEnd_1898728 := by exact prefixLift 1898728
  have htrace : WordTrace (prefixWord ++ tailWord_1898728) baseStart_1898728 baseEnd_1898728 := by
    simpa [prefixWord, tailWord_1898728, baseEnd_1898728] using wordTrace_append hprefix tailTrace_1898728
  have hstable : (prefixWord ++ tailWord_1898728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898728).length < 2 ^ (prefixWord ++ tailWord_1898728).sum := by decide
  have hdescent : baseEnd_1898728 < baseStart_1898728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898828 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1898828 : Nat := 118140960795 + 1898828 * 2 ^ 59
def prefixEnd_1898828 : Nat := 4983230072969 + 3 ^ 40 * 1898828 * 2
def baseEnd_1898828 : Nat := 975011444215602060417455

theorem tailTrace_1898828 : CollatzResearch.WordTrace tailWord_1898828 prefixEnd_1898828 975011444215602060417455 := by
  unfold tailWord_1898828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34627973382438962424572569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46170631176585283232763425 34627973382438962424572569)
  ·
    refine ⟨25970980036829221818429427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34627973382438962424572569 25970980036829221818429427)
    ·
      refine ⟨38956470055243832727644141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25970980036829221818429427 38956470055243832727644141)
      ·
        refine ⟨14608676270716437272866553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38956470055243832727644141 14608676270716437272866553)
        ·
          refine ⟨10956507203037327954649915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14608676270716437272866553 10956507203037327954649915)
          ·
            refine ⟨16434760804555991931974873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956507203037327954649915 16434760804555991931974873)
            ·
              refine ⟨12326070603416993948981155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16434760804555991931974873 12326070603416993948981155)
              ·
                refine ⟨18489105905125490923471733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12326070603416993948981155 18489105905125490923471733)
                ·
                  refine ⟨1733353678605514774075475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18489105905125490923471733 1733353678605514774075475)
                  ·
                    refine ⟨2600030517908272161113213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733353678605514774075475 2600030517908272161113213)
                    ·
                      refine ⟨975011444215602060417455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2600030517908272161113213 975011444215602060417455)
                      ·
                        rfl

theorem cell23_1898828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1898828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898828 prefixEnd_1898828 := by exact prefixLift 1898828
  have htrace : WordTrace (prefixWord ++ tailWord_1898828) baseStart_1898828 baseEnd_1898828 := by
    simpa [prefixWord, tailWord_1898828, baseEnd_1898828] using wordTrace_append hprefix tailTrace_1898828
  have hstable : (prefixWord ++ tailWord_1898828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898828).length < 2 ^ (prefixWord ++ tailWord_1898828).sum := by decide
  have hdescent : baseEnd_1898828 < baseStart_1898828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898831 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 1, 5]
def baseStart_1898831 : Nat := 118140960795 + 1898831 * 2 ^ 59
def prefixEnd_1898831 : Nat := 4983230072969 + 3 ^ 40 * 1898831 * 2
def baseEnd_1898831 : Nat := 325004328219188516226647

theorem tailTrace_1898831 : CollatzResearch.WordTrace tailWord_1898831 prefixEnd_1898831 325004328219188516226647 := by
  unfold tailWord_1898831
  simp only [CollatzResearch.WordTrace]
  refine ⟨69256056183867056361504347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46170704122578037574336231 69256056183867056361504347)
  ·
    refine ⟨103884084275800584542256521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69256056183867056361504347 103884084275800584542256521)
    ·
      refine ⟨77913063206850438406692391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103884084275800584542256521 77913063206850438406692391)
      ·
        refine ⟨116869594810275657610038587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77913063206850438406692391 116869594810275657610038587)
        ·
          refine ⟨175304392215413486415057881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116869594810275657610038587 175304392215413486415057881)
          ·
            refine ⟨131478294161560114811293411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175304392215413486415057881 131478294161560114811293411)
            ·
              refine ⟨197217441242340172216940117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131478294161560114811293411 197217441242340172216940117)
              ·
                refine ⟨2311141889558673893167267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 197217441242340172216940117 2311141889558673893167267)
                ·
                  refine ⟨3466712834338010839750901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311141889558673893167267 3466712834338010839750901)
                  ·
                    refine ⟨325004328219188516226647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3466712834338010839750901 325004328219188516226647)
                    ·
                      rfl

theorem cell23_1898831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_1898831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898831 prefixEnd_1898831 := by exact prefixLift 1898831
  have htrace : WordTrace (prefixWord ++ tailWord_1898831) baseStart_1898831 baseEnd_1898831 := by
    simpa [prefixWord, tailWord_1898831, baseEnd_1898831] using wordTrace_append hprefix tailTrace_1898831
  have hstable : (prefixWord ++ tailWord_1898831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898831).length < 2 ^ (prefixWord ++ tailWord_1898831).sum := by decide
  have hdescent : baseEnd_1898831 < baseStart_1898831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898855 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_1898855 : Nat := 118140960795 + 1898855 * 2 ^ 59
def prefixEnd_1898855 : Nat := 4983230072969 + 3 ^ 40 * 1898855 * 2
def baseEnd_1898855 : Nat := 975025308193273454779831

theorem tailTrace_1898855 : CollatzResearch.WordTrace tailWord_1898855 prefixEnd_1898855 975025308193273454779831 := by
  unfold tailWord_1898855
  simp only [CollatzResearch.WordTrace]
  refine ⟨69256931535780108460378019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46171287690520072306918679 69256931535780108460378019)
  ·
    refine ⟨103885397303670162690567029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69256931535780108460378019 103885397303670162690567029)
    ·
      refine ⟨9739255997219077752240659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103885397303670162690567029 9739255997219077752240659)
      ·
        refine ⟨14608883995828616628360989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739255997219077752240659 14608883995828616628360989)
        ·
          refine ⟨5478331498435731235635371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14608883995828616628360989 5478331498435731235635371)
          ·
            refine ⟨8217497247653596853453057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478331498435731235635371 8217497247653596853453057)
            ·
              refine ⟨6163122935740197640089793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217497247653596853453057 6163122935740197640089793)
              ·
                refine ⟨4622342201805148230067345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6163122935740197640089793 4622342201805148230067345)
                ·
                  refine ⟨3466756651353861172550509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622342201805148230067345 3466756651353861172550509)
                  ·
                    refine ⟨1300033744257697939706441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466756651353861172550509 1300033744257697939706441)
                    ·
                      refine ⟨975025308193273454779831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300033744257697939706441 975025308193273454779831)
                      ·
                        rfl

theorem cell23_1898855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_1898855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898855 prefixEnd_1898855 := by exact prefixLift 1898855
  have htrace : WordTrace (prefixWord ++ tailWord_1898855) baseStart_1898855 baseEnd_1898855 := by
    simpa [prefixWord, tailWord_1898855, baseEnd_1898855] using wordTrace_append hprefix tailTrace_1898855
  have hstable : (prefixWord ++ tailWord_1898855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898855).length < 2 ^ (prefixWord ++ tailWord_1898855).sum := by decide
  have hdescent : baseEnd_1898855 < baseStart_1898855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898861 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1898861 : Nat := 118140960795 + 1898861 * 2 ^ 59
def prefixEnd_1898861 : Nat := 4983230072969 + 3 ^ 40 * 1898861 * 2
def baseEnd_1898861 : Nat := 325009463025733477101601

theorem tailTrace_1898861 : CollatzResearch.WordTrace tailWord_1898861 prefixEnd_1898861 325009463025733477101601 := by
  unfold tailWord_1898861
  simp only [CollatzResearch.WordTrace]
  refine ⟨69257150373758371485096437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46171433582505580990064291 69257150373758371485096437)
  ·
    refine ⟨6492857847539847326727791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69257150373758371485096437 6492857847539847326727791)
    ·
      refine ⟨9739286771309770990091687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492857847539847326727791 9739286771309770990091687)
      ·
        refine ⟨14608930156964656485137531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739286771309770990091687 14608930156964656485137531)
        ·
          refine ⟨21913395235446984727706297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14608930156964656485137531 21913395235446984727706297)
          ·
            refine ⟨16435046426585238545779723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21913395235446984727706297 16435046426585238545779723)
            ·
              refine ⟨24652569639877857818669585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16435046426585238545779723 24652569639877857818669585)
              ·
                refine ⟨18489427229908393364002189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24652569639877857818669585 18489427229908393364002189)
                ·
                  refine ⟨6933535211215647511500821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18489427229908393364002189 6933535211215647511500821)
                  ·
                    refine ⟨325009463025733477101601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6933535211215647511500821 325009463025733477101601)
                    ·
                      rfl

theorem cell23_1898861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1898861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898861 prefixEnd_1898861 := by exact prefixLift 1898861
  have htrace : WordTrace (prefixWord ++ tailWord_1898861) baseStart_1898861 baseEnd_1898861 := by
    simpa [prefixWord, tailWord_1898861, baseEnd_1898861] using wordTrace_append hprefix tailTrace_1898861
  have hstable : (prefixWord ++ tailWord_1898861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898861).length < 2 ^ (prefixWord ++ tailWord_1898861).sum := by decide
  have hdescent : baseEnd_1898861 < baseStart_1898861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898888 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1898888 : Nat := 118140960795 + 1898888 * 2 ^ 59
def prefixEnd_1898888 : Nat := 4983230072969 + 3 ^ 40 * 1898888 * 2
def baseEnd_1898888 : Nat := 975042253054871825667179

theorem tailTrace_1898888 : CollatzResearch.WordTrace tailWord_1898888 prefixEnd_1898888 975042253054871825667179 := by
  unfold tailWord_1898888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629067572330277548164659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46172090096440370064219545 34629067572330277548164659)
  ·
    refine ⟨51943601358495416322246989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34629067572330277548164659 51943601358495416322246989)
    ·
      refine ⟨19478850509435781120842621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51943601358495416322246989 19478850509435781120842621)
      ·
        refine ⟨7304568941038417920315983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19478850509435781120842621 7304568941038417920315983)
        ·
          refine ⟨10956853411557626880473975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304568941038417920315983 10956853411557626880473975)
          ·
            refine ⟨16435280117336440320710963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10956853411557626880473975 16435280117336440320710963)
            ·
              refine ⟨24652920176004660481066445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16435280117336440320710963 24652920176004660481066445)
              ·
                refine ⟨9244845066001747680399917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24652920176004660481066445 9244845066001747680399917)
                ·
                  refine ⟨3466816899750655380149969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9244845066001747680399917 3466816899750655380149969)
                  ·
                    refine ⟨2600112674812991535112477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3466816899750655380149969 2600112674812991535112477)
                    ·
                      refine ⟨975042253054871825667179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2600112674812991535112477 975042253054871825667179)
                      ·
                        rfl

theorem cell23_1898888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1898888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898888 prefixEnd_1898888 := by exact prefixLift 1898888
  have htrace : WordTrace (prefixWord ++ tailWord_1898888) baseStart_1898888 baseEnd_1898888 := by
    simpa [prefixWord, tailWord_1898888, baseEnd_1898888] using wordTrace_append hprefix tailTrace_1898888
  have hstable : (prefixWord ++ tailWord_1898888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898888).length < 2 ^ (prefixWord ++ tailWord_1898888).sum := by decide
  have hdescent : baseEnd_1898888 < baseStart_1898888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898919 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1898919 : Nat := 118140960795 + 1898919 * 2 ^ 59
def prefixEnd_1898919 : Nat := 4983230072969 + 3 ^ 40 * 1898919 * 2
def baseEnd_1898919 : Nat := 975058170955161204379537

theorem tailTrace_1898919 : CollatzResearch.WordTrace tailWord_1898919 prefixEnd_1898919 975058170955161204379537 := by
  unfold tailWord_1898919
  simp only [CollatzResearch.WordTrace]
  refine ⟨69259265807548247390707811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46172843871698831593805207 69259265807548247390707811)
  ·
    refine ⟨103888898711322371086061717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69259265807548247390707811 103888898711322371086061717)
    ·
      refine ⟨4869792127093236144659143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103888898711322371086061717 4869792127093236144659143)
      ·
        refine ⟨7304688190639854216988715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869792127093236144659143 7304688190639854216988715)
        ·
          refine ⟨10957032285959781325483073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304688190639854216988715 10957032285959781325483073)
          ·
            refine ⟨8217774214469835994112305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10957032285959781325483073 8217774214469835994112305)
            ·
              refine ⟨6163330660852376995584229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217774214469835994112305 6163330660852376995584229)
              ·
                refine ⟨1155624498909820686672043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6163330660852376995584229 1155624498909820686672043)
                ·
                  refine ⟨1733436748364731030008065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155624498909820686672043 1733436748364731030008065)
                  ·
                    refine ⟨1300077561273548272506049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1733436748364731030008065 1300077561273548272506049)
                    ·
                      refine ⟨975058170955161204379537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300077561273548272506049 975058170955161204379537)
                      ·
                        rfl

theorem cell23_1898919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1898919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898919 prefixEnd_1898919 := by exact prefixLift 1898919
  have htrace : WordTrace (prefixWord ++ tailWord_1898919) baseStart_1898919 baseEnd_1898919 := by
    simpa [prefixWord, tailWord_1898919, baseEnd_1898919] using wordTrace_append hprefix tailTrace_1898919
  have hstable : (prefixWord ++ tailWord_1898919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898919).length < 2 ^ (prefixWord ++ tailWord_1898919).sum := by decide
  have hdescent : baseEnd_1898919 < baseStart_1898919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898932 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1898932 : Nat := 118140960795 + 1898932 * 2 ^ 59
def prefixEnd_1898932 : Nat := 4983230072969 + 3 ^ 40 * 1898932 * 2
def baseEnd_1898932 : Nat := 975064846203669653516977

theorem tailTrace_1898932 : CollatzResearch.WordTrace tailWord_1898932 prefixEnd_1898932 975064846203669653516977 := by
  unfold tailWord_1898932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629869978250575305465525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46173159971000767073954033 34629869978250575305465525)
  ·
    refine ⟨3246550310460991434887393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34629869978250575305465525 3246550310460991434887393)
    ·
      refine ⟨2434912732845743576165545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246550310460991434887393 2434912732845743576165545)
      ·
        refine ⟨1826184549634307682124159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434912732845743576165545 1826184549634307682124159)
        ·
          refine ⟨2739276824451461523186239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826184549634307682124159 2739276824451461523186239)
          ·
            refine ⟨4108915236677192284779359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739276824451461523186239 4108915236677192284779359)
            ·
              refine ⟨6163372855015788427169039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108915236677192284779359 6163372855015788427169039)
              ·
                refine ⟨9245059282523682640753559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6163372855015788427169039 9245059282523682640753559)
                ·
                  refine ⟨13867588923785523961130339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9245059282523682640753559 13867588923785523961130339)
                  ·
                    refine ⟨20801383385678285941695509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13867588923785523961130339 20801383385678285941695509)
                    ·
                      refine ⟨975064846203669653516977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20801383385678285941695509 975064846203669653516977)
                      ·
                        rfl

theorem cell23_1898932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1898932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898932 prefixEnd_1898932 := by exact prefixLift 1898932
  have htrace : WordTrace (prefixWord ++ tailWord_1898932) baseStart_1898932 baseEnd_1898932 := by
    simpa [prefixWord, tailWord_1898932, baseEnd_1898932] using wordTrace_append hprefix tailTrace_1898932
  have hstable : (prefixWord ++ tailWord_1898932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898932).length < 2 ^ (prefixWord ++ tailWord_1898932).sum := by decide
  have hdescent : baseEnd_1898932 < baseStart_1898932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898935 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_1898935 : Nat := 118140960795 + 1898935 * 2 ^ 59
def prefixEnd_1898935 : Nat := 4983230072969 + 3 ^ 40 * 1898935 * 2
def baseEnd_1898935 : Nat := 975066386645633141779463

theorem tailTrace_1898935 : CollatzResearch.WordTrace tailWord_1898935 prefixEnd_1898935 975066386645633141779463 := by
  unfold tailWord_1898935
  simp only [CollatzResearch.WordTrace]
  refine ⟨69259849375490282123290259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46173232916993521415526839 69259849375490282123290259)
  ·
    refine ⟨103889774063235423184935389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69259849375490282123290259 103889774063235423184935389)
    ·
      refine ⟨38958665273713283694350771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103889774063235423184935389 38958665273713283694350771)
      ·
        refine ⟨58437997910569925541526157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38958665273713283694350771 58437997910569925541526157)
        ·
          refine ⟨21914249216463722078072309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58437997910569925541526157 21914249216463722078072309)
          ·
            refine ⟨2054460864043473944819279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21914249216463722078072309 2054460864043473944819279)
            ·
              refine ⟨3081691296065210917228919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054460864043473944819279 3081691296065210917228919)
              ·
                refine ⟨4622536944097816375843379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081691296065210917228919 4622536944097816375843379)
                ·
                  refine ⟨6933805416146724563765069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622536944097816375843379 6933805416146724563765069)
                  ·
                    refine ⟨2600177031055021711411901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6933805416146724563765069 2600177031055021711411901)
                    ·
                      refine ⟨975066386645633141779463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2600177031055021711411901 975066386645633141779463)
                      ·
                        rfl

theorem cell23_1898935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_1898935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898935 prefixEnd_1898935 := by exact prefixLift 1898935
  have htrace : WordTrace (prefixWord ++ tailWord_1898935) baseStart_1898935 baseEnd_1898935 := by
    simpa [prefixWord, tailWord_1898935, baseEnd_1898935] using wordTrace_append hprefix tailTrace_1898935
  have hstable : (prefixWord ++ tailWord_1898935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898935).length < 2 ^ (prefixWord ++ tailWord_1898935).sum := by decide
  have hdescent : baseEnd_1898935 < baseStart_1898935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898992 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2]
def baseStart_1898992 : Nat := 118140960795 + 1898992 * 2 ^ 59
def prefixEnd_1898992 : Nat := 4983230072969 + 3 ^ 40 * 1898992 * 2
def baseEnd_1898992 : Nat := 975095655042939418766701

theorem tailTrace_1898992 : CollatzResearch.WordTrace tailWord_1898992 prefixEnd_1898992 975095655042939418766701 := by
  unfold tailWord_1898992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34630964168141890429057615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46174618890855853905410153 34630964168141890429057615)
  ·
    refine ⟨51946446252212835643586423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34630964168141890429057615 51946446252212835643586423)
    ·
      refine ⟨77919669378319253465379635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51946446252212835643586423 77919669378319253465379635)
      ·
        refine ⟨116879504067478880198069453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77919669378319253465379635 116879504067478880198069453)
        ·
          refine ⟨43829814025304580074276045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116879504067478880198069453 43829814025304580074276045)
          ·
            refine ⟨16436180259489217527853517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43829814025304580074276045 16436180259489217527853517)
            ·
              refine ⟨6163567597308456572945069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16436180259489217527853517 6163567597308456572945069)
              ·
                refine ⟨2311337848990671214854401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6163567597308456572945069 2311337848990671214854401)
                ·
                  refine ⟨1733503386743003411140801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2311337848990671214854401 1733503386743003411140801)
                  ·
                    refine ⟨1300127540057252558355601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1733503386743003411140801 1300127540057252558355601)
                    ·
                      refine ⟨975095655042939418766701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300127540057252558355601 975095655042939418766701)
                      ·
                        rfl

theorem cell23_1898992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2].length) (baseStart_1898992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898992 prefixEnd_1898992 := by exact prefixLift 1898992
  have htrace : WordTrace (prefixWord ++ tailWord_1898992) baseStart_1898992 baseEnd_1898992 := by
    simpa [prefixWord, tailWord_1898992, baseEnd_1898992] using wordTrace_append hprefix tailTrace_1898992
  have hstable : (prefixWord ++ tailWord_1898992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898992).length < 2 ^ (prefixWord ++ tailWord_1898992).sum := by decide
  have hdescent : baseEnd_1898992 < baseStart_1898992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898998 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1898998 : Nat := 118140960795 + 1898998 * 2 ^ 59
def prefixEnd_1898998 : Nat := 4983230072969 + 3 ^ 40 * 1898998 * 2
def baseEnd_1898998 : Nat := 108344303991874043921297

theorem tailTrace_1898998 : CollatzResearch.WordTrace tailWord_1898998 prefixEnd_1898998 108344303991874043921297 := by
  unfold tailWord_1898998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328884198391377742677103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46174764782841362588555765 4328884198391377742677103)
  ·
    refine ⟨6493326297587066614015655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328884198391377742677103 6493326297587066614015655)
    ·
      refine ⟨9739989446380599921023483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6493326297587066614015655 9739989446380599921023483)
      ·
        refine ⟨14609984169570899881535225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739989446380599921023483 14609984169570899881535225)
        ·
          refine ⟨10957488127178174911151419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14609984169570899881535225 10957488127178174911151419)
          ·
            refine ⟨16436232190767262366727129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957488127178174911151419 16436232190767262366727129)
            ·
              refine ⟨12327174143075446775045347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16436232190767262366727129 12327174143075446775045347)
              ·
                refine ⟨18490761214613170162568021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327174143075446775045347 18490761214613170162568021)
                ·
                  refine ⟨108344303991874043921297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18490761214613170162568021 108344303991874043921297)
                  ·
                    rfl

theorem cell23_1898998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1898998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1898998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1898998 prefixEnd_1898998 := by exact prefixLift 1898998
  have htrace : WordTrace (prefixWord ++ tailWord_1898998) baseStart_1898998 baseEnd_1898998 := by
    simpa [prefixWord, tailWord_1898998, baseEnd_1898998] using wordTrace_append hprefix tailTrace_1898998
  have hstable : (prefixWord ++ tailWord_1898998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898998).length < 2 ^ (prefixWord ++ tailWord_1898998).sum := by decide
  have hdescent : baseEnd_1898998 < baseStart_1898998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899032 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 5]
def baseStart_1899032 : Nat := 118140960795 + 1899032 * 2 ^ 59
def prefixEnd_1899032 : Nat := 4983230072969 + 3 ^ 40 * 1899032 * 2
def baseEnd_1899032 : Nat := 108346243807679918029613

theorem tailTrace_1899032 : CollatzResearch.WordTrace tailWord_1899032 prefixEnd_1899032 108346243807679918029613 := by
  unfold tailWord_1899032
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631693628069433844785675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46175591504092578459714233 34631693628069433844785675)
  ·
    refine ⟨51947540442104150767178513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34631693628069433844785675 51947540442104150767178513)
    ·
      refine ⟨38960655331578113075383885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51947540442104150767178513 38960655331578113075383885)
      ·
        refine ⟨14610245749341792403268957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38960655331578113075383885 14610245749341792403268957)
        ·
          refine ⟨5478842156003172151225859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14610245749341792403268957 5478842156003172151225859)
          ·
            refine ⟨8218263234004758226838789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478842156003172151225859 8218263234004758226838789)
            ·
              refine ⟨1540924356375892167532273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8218263234004758226838789 1540924356375892167532273)
              ·
                refine ⟨1155693267281919125649205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540924356375892167532273 1155693267281919125649205)
                ·
                  refine ⟨108346243807679918029613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1155693267281919125649205 108346243807679918029613)
                  ·
                    rfl

theorem cell23_1899032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 5].length) (baseStart_1899032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899032 prefixEnd_1899032 := by exact prefixLift 1899032
  have htrace : WordTrace (prefixWord ++ tailWord_1899032) baseStart_1899032 baseEnd_1899032 := by
    simpa [prefixWord, tailWord_1899032, baseEnd_1899032] using wordTrace_append hprefix tailTrace_1899032
  have hstable : (prefixWord ++ tailWord_1899032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899032).length < 2 ^ (prefixWord ++ tailWord_1899032).sum := by decide
  have hdescent : baseEnd_1899032 < baseStart_1899032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899062 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1899062 : Nat := 118140960795 + 1899062 * 2 ^ 59
def prefixEnd_1899062 : Nat := 4983230072969 + 3 ^ 40 * 1899062 * 2
def baseEnd_1899062 : Nat := 325043866229584714963793

theorem tailTrace_1899062 : CollatzResearch.WordTrace tailWord_1899062 prefixEnd_1899062 325043866229584714963793 := by
  unfold tailWord_1899062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329030090376886425822715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46176320964020121875442293 4329030090376886425822715)
  ·
    refine ⟨6493545135565329638734073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329030090376886425822715 6493545135565329638734073)
    ·
      refine ⟨4870158851673997229050555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6493545135565329638734073 4870158851673997229050555)
      ·
        refine ⟨7305238277510995843575833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870158851673997229050555 7305238277510995843575833)
        ·
          refine ⟨5478928708133246882681875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7305238277510995843575833 5478928708133246882681875)
          ·
            refine ⟨8218393062199870324022813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478928708133246882681875 8218393062199870324022813)
            ·
              refine ⟨3081897398324951371508555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8218393062199870324022813 3081897398324951371508555)
              ·
                refine ⟨4622846097487427057262833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081897398324951371508555 4622846097487427057262833)
                ·
                  refine ⟨3467134573115570292947125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622846097487427057262833 3467134573115570292947125)
                  ·
                    refine ⟨325043866229584714963793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3467134573115570292947125 325043866229584714963793)
                    ·
                      rfl

theorem cell23_1899062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1899062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899062 prefixEnd_1899062 := by exact prefixLift 1899062
  have htrace : WordTrace (prefixWord ++ tailWord_1899062) baseStart_1899062 baseEnd_1899062 := by
    simpa [prefixWord, tailWord_1899062, baseEnd_1899062] using wordTrace_append hprefix tailTrace_1899062
  have hstable : (prefixWord ++ tailWord_1899062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899062).length < 2 ^ (prefixWord ++ tailWord_1899062).sum := by decide
  have hdescent : baseEnd_1899062 < baseStart_1899062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899065 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1899065 : Nat := 118140960795 + 1899065 * 2 ^ 59
def prefixEnd_1899065 : Nat := 4983230072969 + 3 ^ 40 * 1899065 * 2
def baseEnd_1899065 : Nat := 975133139130717633153865

theorem tailTrace_1899065 : CollatzResearch.WordTrace tailWord_1899065 prefixEnd_1899065 975133139130717633153865 := by
  unfold tailWord_1899065
  simp only [CollatzResearch.WordTrace]
  refine ⟨69264590865019314325522649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46176393910012876217015099 69264590865019314325522649)
  ·
    refine ⟨51948443148764485744141987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69264590865019314325522649 51948443148764485744141987)
    ·
      refine ⟨77922664723146728616212981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51948443148764485744141987 77922664723146728616212981)
      ·
        refine ⟨7305249817795005807769967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77922664723146728616212981 7305249817795005807769967)
        ·
          refine ⟨10957874726692508711654951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7305249817795005807769967 10957874726692508711654951)
          ·
            refine ⟨16436812090038763067482427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10957874726692508711654951 16436812090038763067482427)
            ·
              refine ⟨24655218135058144601223641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16436812090038763067482427 24655218135058144601223641)
              ·
                refine ⟨18491413601293608450917731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24655218135058144601223641 18491413601293608450917731)
                ·
                  refine ⟨27737120401940412676376597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18491413601293608450917731 27737120401940412676376597)
                  ·
                    refine ⟨1300177518840956844205153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27737120401940412676376597 1300177518840956844205153)
                    ·
                      refine ⟨975133139130717633153865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300177518840956844205153 975133139130717633153865)
                      ·
                        rfl

theorem cell23_1899065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1899065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899065 prefixEnd_1899065 := by exact prefixLift 1899065
  have htrace : WordTrace (prefixWord ++ tailWord_1899065) baseStart_1899065 baseEnd_1899065 := by
    simpa [prefixWord, tailWord_1899065, baseEnd_1899065] using wordTrace_append hprefix tailTrace_1899065
  have hstable : (prefixWord ++ tailWord_1899065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899065).length < 2 ^ (prefixWord ++ tailWord_1899065).sum := by decide
  have hdescent : baseEnd_1899065 < baseStart_1899065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899088 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 6]
def baseStart_1899088 : Nat := 118140960795 + 1899088 * 2 ^ 59
def prefixEnd_1899088 : Nat := 4983230072969 + 3 ^ 40 * 1899088 * 2
def baseEnd_1899088 : Nat := 108349438798419004796251

theorem tailTrace_1899088 : CollatzResearch.WordTrace tailWord_1899088 prefixEnd_1899088 108349438798419004796251 := by
  unfold tailWord_1899088
  simp only [CollatzResearch.WordTrace]
  refine ⟨34632714871967994626804959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46176953162623992835739945 34632714871967994626804959)
  ·
    refine ⟨51949072307951991940207439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34632714871967994626804959 51949072307951991940207439)
    ·
      refine ⟨77923608461927987910311159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51949072307951991940207439 77923608461927987910311159)
      ·
        refine ⟨116885412692891981865466739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77923608461927987910311159 116885412692891981865466739)
        ·
          refine ⟨175328119039337972798200109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116885412692891981865466739 175328119039337972798200109)
          ·
            refine ⟨65748044639751739799325041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175328119039337972798200109 65748044639751739799325041)
            ·
              refine ⟨49311033479813804849493781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65748044639751739799325041 49311033479813804849493781)
              ·
                refine ⟨2311454694366272102320021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49311033479813804849493781 2311454694366272102320021)
                ·
                  refine ⟨108349438798419004796251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2311454694366272102320021 108349438798419004796251)
                  ·
                    rfl

theorem cell23_1899088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 6].length) (baseStart_1899088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899088 prefixEnd_1899088 := by exact prefixLift 1899088
  have htrace : WordTrace (prefixWord ++ tailWord_1899088) baseStart_1899088 baseEnd_1899088 := by
    simpa [prefixWord, tailWord_1899088, baseEnd_1899088] using wordTrace_append hprefix tailTrace_1899088
  have hstable : (prefixWord ++ tailWord_1899088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899088).length < 2 ^ (prefixWord ++ tailWord_1899088).sum := by decide
  have hdescent : baseEnd_1899088 < baseStart_1899088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899092 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1899092 : Nat := 118140960795 + 1899092 * 2 ^ 59
def prefixEnd_1899092 : Nat := 4983230072969 + 3 ^ 40 * 1899092 * 2
def baseEnd_1899092 : Nat := 325049001036129675838747

theorem tailTrace_1899092 : CollatzResearch.WordTrace tailWord_1899092 prefixEnd_1899092 325049001036129675838747 := by
  unfold tailWord_1899092
  simp only [CollatzResearch.WordTrace]
  refine ⟨34632787817960748968377765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46177050423947665291170353 34632787817960748968377765)
  ·
    refine ⟨6493647715867640431570831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34632787817960748968377765 6493647715867640431570831)
    ·
      refine ⟨9740471573801460647356247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6493647715867640431570831 9740471573801460647356247)
      ·
        refine ⟨14610707360702190971034371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9740471573801460647356247 14610707360702190971034371)
        ·
          refine ⟨21916061041053286456551557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14610707360702190971034371 21916061041053286456551557)
          ·
            refine ⟨4109261445197491210603417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21916061041053286456551557 4109261445197491210603417)
            ·
              refine ⟨3081946083898118407952563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109261445197491210603417 3081946083898118407952563)
              ·
                refine ⟨4622919125847177611928845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081946083898118407952563 4622919125847177611928845)
                ·
                  refine ⟨1733594672192691604473317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4622919125847177611928845 1733594672192691604473317)
                  ·
                    refine ⟨325049001036129675838747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1733594672192691604473317 325049001036129675838747)
                    ·
                      rfl

theorem cell23_1899092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1899092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899092 prefixEnd_1899092 := by exact prefixLift 1899092
  have htrace : WordTrace (prefixWord ++ tailWord_1899092) baseStart_1899092 baseEnd_1899092 := by
    simpa [prefixWord, tailWord_1899092, baseEnd_1899092] using wordTrace_append hprefix tailTrace_1899092
  have hstable : (prefixWord ++ tailWord_1899092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899092).length < 2 ^ (prefixWord ++ tailWord_1899092).sum := by decide
  have hdescent : baseEnd_1899092 < baseStart_1899092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899108 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1899108 : Nat := 118140960795 + 1899108 * 2 ^ 59
def prefixEnd_1899108 : Nat := 4983230072969 + 3 ^ 40 * 1899108 * 2
def baseEnd_1899108 : Nat := 975155218798860964916167

theorem tailTrace_1899108 : CollatzResearch.WordTrace tailWord_1899108 prefixEnd_1899108 975155218798860964916167 := by
  unfold tailWord_1899108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34633079601931766334668989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46177439469242355112891985 34633079601931766334668989)
  ·
    refine ⟨12987404850724412375500871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34633079601931766334668989 12987404850724412375500871)
    ·
      refine ⟨19481107276086618563251307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12987404850724412375500871 19481107276086618563251307)
      ·
        refine ⟨29221660914129927844876961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19481107276086618563251307 29221660914129927844876961)
        ·
          refine ⟨21916245685597445883657721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29221660914129927844876961 21916245685597445883657721)
          ·
            refine ⟨16437184264198084412743291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21916245685597445883657721 16437184264198084412743291)
            ·
              refine ⟨24655776396297126619114937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16437184264198084412743291 24655776396297126619114937)
              ·
                refine ⟨18491832297222844964336203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24655776396297126619114937 18491832297222844964336203)
                ·
                  refine ⟨27737748445834267446504305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18491832297222844964336203 27737748445834267446504305)
                  ·
                    refine ⟨20803311334375700584878229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27737748445834267446504305 20803311334375700584878229)
                    ·
                      refine ⟨975155218798860964916167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20803311334375700584878229 975155218798860964916167)
                      ·
                        rfl

theorem cell23_1899108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1899108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899108 prefixEnd_1899108 := by exact prefixLift 1899108
  have htrace : WordTrace (prefixWord ++ tailWord_1899108) baseStart_1899108 baseEnd_1899108 := by
    simpa [prefixWord, tailWord_1899108, baseEnd_1899108] using wordTrace_append hprefix tailTrace_1899108
  have hstable : (prefixWord ++ tailWord_1899108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899108).length < 2 ^ (prefixWord ++ tailWord_1899108).sum := by decide
  have hdescent : baseEnd_1899108 < baseStart_1899108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899115 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 3]
def baseStart_1899115 : Nat := 118140960795 + 1899115 * 2 ^ 59
def prefixEnd_1899115 : Nat := 4983230072969 + 3 ^ 40 * 1899115 * 2
def baseEnd_1899115 : Nat := 975158813163442437528635

theorem tailTrace_1899115 : CollatzResearch.WordTrace tailWord_1899115 prefixEnd_1899115 975158813163442437528635 := by
  unfold tailWord_1899115
  simp only [CollatzResearch.WordTrace]
  refine ⟨69266414514838172864842799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46177609676558781909895199 69266414514838172864842799)
  ·
    refine ⟨103899621772257259297264199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69266414514838172864842799 103899621772257259297264199)
    ·
      refine ⟨155849432658385888945896299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103899621772257259297264199 155849432658385888945896299)
      ·
        refine ⟨233774148987578833418844449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155849432658385888945896299 233774148987578833418844449)
        ·
          refine ⟨175330611740684125064133337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233774148987578833418844449 175330611740684125064133337)
          ·
            refine ⟨131497958805513093798100003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175330611740684125064133337 131497958805513093798100003)
            ·
              refine ⟨197246938208269640697150005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131497958805513093798100003 197246938208269640697150005)
              ·
                refine ⟨18491900457025278815357813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197246938208269640697150005 18491900457025278815357813)
                ·
                  refine ⟨1733615667846119888939795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18491900457025278815357813 1733615667846119888939795)
                  ·
                    refine ⟨2600423501769179833409693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733615667846119888939795 2600423501769179833409693)
                    ·
                      refine ⟨975158813163442437528635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2600423501769179833409693 975158813163442437528635)
                      ·
                        rfl

theorem cell23_1899115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 3].length) (baseStart_1899115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899115 prefixEnd_1899115 := by exact prefixLift 1899115
  have htrace : WordTrace (prefixWord ++ tailWord_1899115) baseStart_1899115 baseEnd_1899115 := by
    simpa [prefixWord, tailWord_1899115, baseEnd_1899115] using wordTrace_append hprefix tailTrace_1899115
  have hstable : (prefixWord ++ tailWord_1899115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899115).length < 2 ^ (prefixWord ++ tailWord_1899115).sum := by decide
  have hdescent : baseEnd_1899115 < baseStart_1899115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899148 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_1899148 : Nat := 118140960795 + 1899148 * 2 ^ 59
def prefixEnd_1899148 : Nat := 4983230072969 + 3 ^ 40 * 1899148 * 2
def baseEnd_1899148 : Nat := 325058586008346936138661

theorem tailTrace_1899148 : CollatzResearch.WordTrace tailWord_1899148 prefixEnd_1899148 325058586008346936138661 := by
  unfold tailWord_1899148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34633809061859309750397049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46178412082479079667196065 34633809061859309750397049)
  ·
    refine ⟨25975356796394482312797787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34633809061859309750397049 25975356796394482312797787)
    ·
      refine ⟨38963035194591723469196681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25975356796394482312797787 38963035194591723469196681)
      ·
        refine ⟨29222276395943792601897511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38963035194591723469196681 29222276395943792601897511)
        ·
          refine ⟨43833414593915688902846267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29222276395943792601897511 43833414593915688902846267)
          ·
            refine ⟨65750121890873533354269401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43833414593915688902846267 65750121890873533354269401)
            ·
              refine ⟨49312591418155150015702051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65750121890873533354269401 49312591418155150015702051)
              ·
                refine ⟨73968887127232725023553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49312591418155150015702051 73968887127232725023553077)
                ·
                  refine ⟨6934583168178067970958101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73968887127232725023553077 6934583168178067970958101)
                  ·
                    refine ⟨325058586008346936138661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6934583168178067970958101 325058586008346936138661)
                    ·
                      rfl

theorem cell23_1899148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_1899148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899148 prefixEnd_1899148 := by exact prefixLift 1899148
  have htrace : WordTrace (prefixWord ++ tailWord_1899148) baseStart_1899148 baseEnd_1899148 := by
    simpa [prefixWord, tailWord_1899148, baseEnd_1899148] using wordTrace_append hprefix tailTrace_1899148
  have hstable : (prefixWord ++ tailWord_1899148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899148).length < 2 ^ (prefixWord ++ tailWord_1899148).sum := by decide
  have hdescent : baseEnd_1899148 < baseStart_1899148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899169 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_1899169 : Nat := 118140960795 + 1899169 * 2 ^ 59
def prefixEnd_1899169 : Nat := 4983230072969 + 3 ^ 40 * 1899169 * 2
def baseEnd_1899169 : Nat := 325062180372928408751129

theorem tailTrace_1899169 : CollatzResearch.WordTrace tailWord_1899169 prefixEnd_1899169 325062180372928408751129 := by
  unfold tailWord_1899169
  simp only [CollatzResearch.WordTrace]
  refine ⟨69268384056642540087308561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46178922704428360058205707 69268384056642540087308561)
  ·
    refine ⟨51951288042481905065481421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69268384056642540087308561 51951288042481905065481421)
    ·
      refine ⟨19481733015930714399555533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51951288042481905065481421 19481733015930714399555533)
      ·
        refine ⟨7305649880974017899833325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19481733015930714399555533 7305649880974017899833325)
        ·
          refine ⟨2739618705365256712437497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7305649880974017899833325 2739618705365256712437497)
          ·
            refine ⟨2054714029023942534328123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2739618705365256712437497 2054714029023942534328123)
            ·
              refine ⟨3082071043535913801492185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054714029023942534328123 3082071043535913801492185)
              ·
                refine ⟨2311553282651935351119139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082071043535913801492185 2311553282651935351119139)
                ·
                  refine ⟨3467329923977903026678709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311553282651935351119139 3467329923977903026678709)
                  ·
                    refine ⟨325062180372928408751129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3467329923977903026678709 325062180372928408751129)
                    ·
                      rfl

theorem cell23_1899169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_1899169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899169 prefixEnd_1899169 := by exact prefixLift 1899169
  have htrace : WordTrace (prefixWord ++ tailWord_1899169) baseStart_1899169 baseEnd_1899169 := by
    simpa [prefixWord, tailWord_1899169, baseEnd_1899169] using wordTrace_append hprefix tailTrace_1899169
  have hstable : (prefixWord ++ tailWord_1899169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899169).length < 2 ^ (prefixWord ++ tailWord_1899169).sum := by decide
  have hdescent : baseEnd_1899169 < baseStart_1899169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899182 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1899182 : Nat := 118140960795 + 1899182 * 2 ^ 59
def prefixEnd_1899182 : Nat := 4983230072969 + 3 ^ 40 * 1899182 * 2
def baseEnd_1899182 : Nat := 325064405455764558463609

theorem tailTrace_1899182 : CollatzResearch.WordTrace tailWord_1899182 prefixEnd_1899182 325064405455764558463609 := by
  unfold tailWord_1899182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658607275699430413441475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46179238803730295538354533 8658607275699430413441475)
  ·
    refine ⟨12987910913549145620162213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8658607275699430413441475 12987910913549145620162213)
    ·
      refine ⟨2435233296290464803780415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12987910913549145620162213 2435233296290464803780415)
      ·
        refine ⟨3652849944435697205670623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435233296290464803780415 3652849944435697205670623)
        ·
          refine ⟨5479274916653545808505935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652849944435697205670623 5479274916653545808505935)
          ·
            refine ⟨8218912374980318712758903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479274916653545808505935 8218912374980318712758903)
            ·
              refine ⟨12328368562470478069138355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218912374980318712758903 12328368562470478069138355)
              ·
                refine ⟨18492552843705717103707533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12328368562470478069138355 18492552843705717103707533)
                ·
                  refine ⟨6934707316389643913890325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18492552843705717103707533 6934707316389643913890325)
                  ·
                    refine ⟨325064405455764558463609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6934707316389643913890325 325064405455764558463609)
                    ·
                      rfl

theorem cell23_1899182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1899182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899182 prefixEnd_1899182 := by exact prefixLift 1899182
  have htrace : WordTrace (prefixWord ++ tailWord_1899182) baseStart_1899182 baseEnd_1899182 := by
    simpa [prefixWord, tailWord_1899182, baseEnd_1899182] using wordTrace_append hprefix tailTrace_1899182
  have hstable : (prefixWord ++ tailWord_1899182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899182).length < 2 ^ (prefixWord ++ tailWord_1899182).sum := by decide
  have hdescent : baseEnd_1899182 < baseStart_1899182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899212 : List Nat := [2, 2, 1, 5, 1, 3, 1, 8]
def baseStart_1899212 : Nat := 118140960795 + 1899212 * 2 ^ 59
def prefixEnd_1899212 : Nat := 4983230072969 + 3 ^ 40 * 1899212 * 2
def baseEnd_1899212 : Nat := 36118837806923279926507

theorem tailTrace_1899212 : CollatzResearch.WordTrace tailWord_1899212 prefixEnd_1899212 36118837806923279926507 := by
  unfold tailWord_1899212
  simp only [CollatzResearch.WordTrace]
  refine ⟨34634976197743379215561945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46179968263657838954082593 34634976197743379215561945)
  ·
    refine ⟨25976232148307534411671459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34634976197743379215561945 25976232148307534411671459)
    ·
      refine ⟨38964348222461301617507189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25976232148307534411671459 38964348222461301617507189)
      ·
        refine ⟨3652907645855747026641299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38964348222461301617507189 3652907645855747026641299)
        ·
          refine ⟨5479361468783620539961949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652907645855747026641299 5479361468783620539961949)
          ·
            refine ⟨2054760550793857702485731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5479361468783620539961949 2054760550793857702485731)
            ·
              refine ⟨3082140826190786553728597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054760550793857702485731 3082140826190786553728597)
              ·
                refine ⟨36118837806923279926507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3082140826190786553728597 36118837806923279926507)
                ·
                  rfl

theorem cell23_1899212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 8].length) (baseStart_1899212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899212 prefixEnd_1899212 := by exact prefixLift 1899212
  have htrace : WordTrace (prefixWord ++ tailWord_1899212) baseStart_1899212 baseEnd_1899212 := by
    simpa [prefixWord, tailWord_1899212, baseEnd_1899212] using wordTrace_append hprefix tailTrace_1899212
  have hstable : (prefixWord ++ tailWord_1899212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899212).length < 2 ^ (prefixWord ++ tailWord_1899212).sum := by decide
  have hdescent : baseEnd_1899212 < baseStart_1899212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899249 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_1899249 : Nat := 118140960795 + 1899249 * 2 ^ 59
def prefixEnd_1899249 : Nat := 4983230072969 + 3 ^ 40 * 1899249 * 2
def baseEnd_1899249 : Nat := 975227619571144913253019

theorem tailTrace_1899249 : CollatzResearch.WordTrace tailWord_1899249 prefixEnd_1899249 975227619571144913253019 := by
  unfold tailWord_1899249
  simp only [CollatzResearch.WordTrace]
  refine ⟨69271301896352713750220801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46180867930901809166813867 69271301896352713750220801)
  ·
    refine ⟨51953476422264535312665601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69271301896352713750220801 51953476422264535312665601)
    ·
      refine ⟨38965107316698401484499201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51953476422264535312665601 38965107316698401484499201)
      ·
        refine ⟨29223830487523801113374401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38965107316698401484499201 29223830487523801113374401)
        ·
          refine ⟨21917872865642850835030801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29223830487523801113374401 21917872865642850835030801)
          ·
            refine ⟨16438404649232138126273101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21917872865642850835030801 16438404649232138126273101)
            ·
              refine ⟨6164401743462051797352413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16438404649232138126273101 6164401743462051797352413)
              ·
                refine ⟨2311650653798269424007155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6164401743462051797352413 2311650653798269424007155)
                ·
                  refine ⟨3467475980697404136010733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311650653798269424007155 3467475980697404136010733)
                  ·
                    refine ⟨1300303492761526551004025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467475980697404136010733 1300303492761526551004025)
                    ·
                      refine ⟨975227619571144913253019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300303492761526551004025 975227619571144913253019)
                      ·
                        rfl

theorem cell23_1899249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_1899249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899249 prefixEnd_1899249 := by exact prefixLift 1899249
  have htrace : WordTrace (prefixWord ++ tailWord_1899249) baseStart_1899249 baseEnd_1899249 := by
    simpa [prefixWord, tailWord_1899249, baseEnd_1899249] using wordTrace_append hprefix tailTrace_1899249
  have hstable : (prefixWord ++ tailWord_1899249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899249).length < 2 ^ (prefixWord ++ tailWord_1899249).sum := by decide
  have hdescent : baseEnd_1899249 < baseStart_1899249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899265 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1899265 : Nat := 118140960795 + 1899265 * 2 ^ 59
def prefixEnd_1899265 : Nat := 4983230072969 + 3 ^ 40 * 1899265 * 2
def baseEnd_1899265 : Nat := 975235835261616850652945

theorem tailTrace_1899265 : CollatzResearch.WordTrace tailWord_1899265 prefixEnd_1899265 975235835261616850652945 := by
  unfold tailWord_1899265
  simp only [CollatzResearch.WordTrace]
  refine ⟨69271885464294748482803249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46181256976196498988535499 69271885464294748482803249)
  ·
    refine ⟨51953914098221061362102437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69271885464294748482803249 51953914098221061362102437)
    ·
      refine ⟨9741358893416449005394207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51953914098221061362102437 9741358893416449005394207)
      ·
        refine ⟨14612038340124673508091311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9741358893416449005394207 14612038340124673508091311)
        ·
          refine ⟨21918057510187010262136967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14612038340124673508091311 21918057510187010262136967)
          ·
            refine ⟨32877086265280515393205451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21918057510187010262136967 32877086265280515393205451)
            ·
              refine ⟨49315629397920773089808177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32877086265280515393205451 49315629397920773089808177)
              ·
                refine ⟨36986722048440579817356133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49315629397920773089808177 36986722048440579817356133)
                ·
                  refine ⟨6935010384082608715754275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36986722048440579817356133 6935010384082608715754275)
                  ·
                    refine ⟨10402515576123913073631413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6935010384082608715754275 10402515576123913073631413)
                    ·
                      refine ⟨975235835261616850652945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10402515576123913073631413 975235835261616850652945)
                      ·
                        rfl

theorem cell23_1899265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1899265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899265 prefixEnd_1899265 := by exact prefixLift 1899265
  have htrace : WordTrace (prefixWord ++ tailWord_1899265) baseStart_1899265 baseEnd_1899265 := by
    simpa [prefixWord, tailWord_1899265, baseEnd_1899265] using wordTrace_append hprefix tailTrace_1899265
  have hstable : (prefixWord ++ tailWord_1899265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899265).length < 2 ^ (prefixWord ++ tailWord_1899265).sum := by decide
  have hdescent : baseEnd_1899265 < baseStart_1899265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899285 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 7]
def baseStart_1899285 : Nat := 118140960795 + 1899285 * 2 ^ 59
def prefixEnd_1899285 : Nat := 4983230072969 + 3 ^ 40 * 1899285 * 2
def baseEnd_1899285 : Nat := 108360678319411863600317

theorem tailTrace_1899285 : CollatzResearch.WordTrace tailWord_1899285 prefixEnd_1899285 108360678319411863600317 := by
  unfold tailWord_1899285
  simp only [CollatzResearch.WordTrace]
  refine ⟨69272614924222291898531309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46181743282814861265687539 69272614924222291898531309)
  ·
    refine ⟨25977230596583359461949241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69272614924222291898531309 25977230596583359461949241)
    ·
      refine ⟨19482922947437519596461931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25977230596583359461949241 19482922947437519596461931)
      ·
        refine ⟨29224384421156279394692897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19482922947437519596461931 29224384421156279394692897)
        ·
          refine ⟨21918288315867209546019673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29224384421156279394692897 21918288315867209546019673)
          ·
            refine ⟨16438716236900407159514755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21918288315867209546019673 16438716236900407159514755)
            ·
              refine ⟨24658074355350610739272133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16438716236900407159514755 24658074355350610739272133)
              ·
                refine ⟨4623388941628239513613525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24658074355350610739272133 4623388941628239513613525)
                ·
                  refine ⟨108360678319411863600317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4623388941628239513613525 108360678319411863600317)
                  ·
                    rfl

theorem cell23_1899285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_1899285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899285 prefixEnd_1899285 := by exact prefixLift 1899285
  have htrace : WordTrace (prefixWord ++ tailWord_1899285) baseStart_1899285 baseEnd_1899285 := by
    simpa [prefixWord, tailWord_1899285, baseEnd_1899285] using wordTrace_append hprefix tailTrace_1899285
  have hstable : (prefixWord ++ tailWord_1899285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899285).length < 2 ^ (prefixWord ++ tailWord_1899285).sum := by decide
  have hdescent : baseEnd_1899285 < baseStart_1899285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899319 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 5]
def baseStart_1899319 : Nat := 118140960795 + 1899319 * 2 ^ 59
def prefixEnd_1899319 : Nat := 4983230072969 + 3 ^ 40 * 1899319 * 2
def baseEnd_1899319 : Nat := 108362618135217737708633

theorem tailTrace_1899319 : CollatzResearch.WordTrace tailWord_1899319 prefixEnd_1899319 108362618135217737708633 := by
  unfold tailWord_1899319
  simp only [CollatzResearch.WordTrace]
  refine ⟨69273855006099115705269011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46182570004066077136846007 69273855006099115705269011)
  ·
    refine ⟨103910782509148673557903517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69273855006099115705269011 103910782509148673557903517)
    ·
      refine ⟨38966543440930752584213819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103910782509148673557903517 38966543440930752584213819)
      ·
        refine ⟨58449815161396128876320729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38966543440930752584213819 58449815161396128876320729)
        ·
          refine ⟨43837361371047096657240547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58449815161396128876320729 43837361371047096657240547)
          ·
            refine ⟨65756042056570644985860821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43837361371047096657240547 65756042056570644985860821)
            ·
              refine ⟨1541157235700874491856113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65756042056570644985860821 1541157235700874491856113)
              ·
                refine ⟨1155867926775655868892085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541157235700874491856113 1155867926775655868892085)
                ·
                  refine ⟨108362618135217737708633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1155867926775655868892085 108362618135217737708633)
                  ·
                    rfl

theorem cell23_1899319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 5].length) (baseStart_1899319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899319 prefixEnd_1899319 := by exact prefixLift 1899319
  have htrace : WordTrace (prefixWord ++ tailWord_1899319) baseStart_1899319 baseEnd_1899319 := by
    simpa [prefixWord, tailWord_1899319, baseEnd_1899319] using wordTrace_append hprefix tailTrace_1899319
  have hstable : (prefixWord ++ tailWord_1899319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899319).length < 2 ^ (prefixWord ++ tailWord_1899319).sum := by decide
  have hdescent : baseEnd_1899319 < baseStart_1899319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899375 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 8]
def baseStart_1899375 : Nat := 118140960795 + 1899375 * 2 ^ 59
def prefixEnd_1899375 : Nat := 4983230072969 + 3 ^ 40 * 1899375 * 2
def baseEnd_1899375 : Nat := 108365813125956824475271

theorem tailTrace_1899375 : CollatzResearch.WordTrace tailWord_1899375 prefixEnd_1899375 108365813125956824475271 := by
  unfold tailWord_1899375
  simp only [CollatzResearch.WordTrace]
  refine ⟨69275897493896237269307579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46183931662597491512871719 69275897493896237269307579)
  ·
    refine ⟨103913846240844355903961369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69275897493896237269307579 103913846240844355903961369)
    ·
      refine ⟨77935384680633266927971027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103913846240844355903961369 77935384680633266927971027)
      ·
        refine ⟨116903077020949900391956541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77935384680633266927971027 116903077020949900391956541)
        ·
          refine ⟨43838653882856212646983703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116903077020949900391956541 43838653882856212646983703)
          ·
            refine ⟨65757980824284318970475555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43838653882856212646983703 65757980824284318970475555)
            ·
              refine ⟨98636971236426478455713333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65757980824284318970475555 98636971236426478455713333)
              ·
                refine ⟨9247216053414982355223125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98636971236426478455713333 9247216053414982355223125)
                ·
                  refine ⟨108365813125956824475271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9247216053414982355223125 108365813125956824475271)
                  ·
                    rfl

theorem cell23_1899375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 8].length) (baseStart_1899375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899375 prefixEnd_1899375 := by exact prefixLift 1899375
  have htrace : WordTrace (prefixWord ++ tailWord_1899375) baseStart_1899375 baseEnd_1899375 := by
    simpa [prefixWord, tailWord_1899375, baseEnd_1899375] using wordTrace_append hprefix tailTrace_1899375
  have hstable : (prefixWord ++ tailWord_1899375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899375).length < 2 ^ (prefixWord ++ tailWord_1899375).sum := by decide
  have hdescent : baseEnd_1899375 < baseStart_1899375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899426 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1899426 : Nat := 118140960795 + 1899426 * 2 ^ 59
def prefixEnd_1899426 : Nat := 4983230072969 + 3 ^ 40 * 1899426 * 2
def baseEnd_1899426 : Nat := 108368722849665635637745

theorem tailTrace_1899426 : CollatzResearch.WordTrace tailWord_1899426 prefixEnd_1899426 108368722849665635637745 := by
  unfold tailWord_1899426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319439404177868244853533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46185171744474315319609421 17319439404177868244853533)
  ·
    refine ⟨6494789776566700591820075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17319439404177868244853533 6494789776566700591820075)
    ·
      refine ⟨9742184664850050887730113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494789776566700591820075 9742184664850050887730113)
      ·
        refine ⟨7306638498637538165797585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9742184664850050887730113 7306638498637538165797585)
        ·
          refine ⟨5479978873978153624348189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7306638498637538165797585 5479978873978153624348189)
          ·
            refine ⟨2054992077741807609130571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5479978873978153624348189 2054992077741807609130571)
            ·
              refine ⟨3082488116612711413695857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054992077741807609130571 3082488116612711413695857)
              ·
                refine ⟨2311866087459533560271893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082488116612711413695857 2311866087459533560271893)
                ·
                  refine ⟨108368722849665635637745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2311866087459533560271893 108368722849665635637745)
                  ·
                    rfl

theorem cell23_1899426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1899426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899426 prefixEnd_1899426 := by exact prefixLift 1899426
  have htrace : WordTrace (prefixWord ++ tailWord_1899426) baseStart_1899426 baseEnd_1899426 := by
    simpa [prefixWord, tailWord_1899426, baseEnd_1899426] using wordTrace_append hprefix tailTrace_1899426
  have hstable : (prefixWord ++ tailWord_1899426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899426).length < 2 ^ (prefixWord ++ tailWord_1899426).sum := by decide
  have hdescent : baseEnd_1899426 < baseStart_1899426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899470 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_1899470 : Nat := 118140960795 + 1899470 * 2 ^ 59
def prefixEnd_1899470 : Nat := 4983230072969 + 3 ^ 40 * 1899470 * 2
def baseEnd_1899470 : Nat := 975341098795788548589503

theorem tailTrace_1899470 : CollatzResearch.WordTrace tailWord_1899470 prefixEnd_1899470 975341098795788548589503 := by
  unfold tailWord_1899470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659920303569008561751983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46186241619034712329343909 8659920303569008561751983)
  ·
    refine ⟨12989880455353512842627975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8659920303569008561751983 12989880455353512842627975)
    ·
      refine ⟨19484820683030269263941963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12989880455353512842627975 19484820683030269263941963)
      ·
        refine ⟨29227231024545403895912945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19484820683030269263941963 29227231024545403895912945)
        ·
          refine ⟨21920423268409052921934709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29227231024545403895912945 21920423268409052921934709)
          ·
            refine ⟨2055039681413348711431379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21920423268409052921934709 2055039681413348711431379)
            ·
              refine ⟨3082559522120023067147069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055039681413348711431379 3082559522120023067147069)
              ·
                refine ⟨1155959820795008650180151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3082559522120023067147069 1155959820795008650180151)
                ·
                  refine ⟨1733939731192512975270227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155959820795008650180151 1733939731192512975270227)
                  ·
                    refine ⟨2600909596788769462905341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1733939731192512975270227 2600909596788769462905341)
                    ·
                      refine ⟨975341098795788548589503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2600909596788769462905341 975341098795788548589503)
                      ·
                        rfl

theorem cell23_1899470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_1899470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899470 prefixEnd_1899470 := by exact prefixLift 1899470
  have htrace : WordTrace (prefixWord ++ tailWord_1899470) baseStart_1899470 baseEnd_1899470 := by
    simpa [prefixWord, tailWord_1899470, baseEnd_1899470] using wordTrace_append hprefix tailTrace_1899470
  have hstable : (prefixWord ++ tailWord_1899470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899470).length < 2 ^ (prefixWord ++ tailWord_1899470).sum := by decide
  have hdescent : baseEnd_1899470 < baseStart_1899470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899472 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_1899472 : Nat := 118140960795 + 1899472 * 2 ^ 59
def prefixEnd_1899472 : Nat := 4983230072969 + 3 ^ 40 * 1899472 * 2
def baseEnd_1899472 : Nat := 975342125757097540764493

theorem tailTrace_1899472 : CollatzResearch.WordTrace tailWord_1899472 prefixEnd_1899472 975342125757097540764493 := by
  unfold tailWord_1899472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34639717687272411417794335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46186290249696548557059113 34639717687272411417794335)
  ·
    refine ⟨51959576530908617126691503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34639717687272411417794335 51959576530908617126691503)
    ·
      refine ⟨77939364796362925690037255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51959576530908617126691503 77939364796362925690037255)
      ·
        refine ⟨116909047194544388535055883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77939364796362925690037255 116909047194544388535055883)
        ·
          refine ⟨175363570791816582802583825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116909047194544388535055883 175363570791816582802583825)
          ·
            refine ⟨131522678093862437101937869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175363570791816582802583825 131522678093862437101937869)
            ·
              refine ⟨49321004285198413913226701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131522678093862437101937869 49321004285198413913226701)
              ·
                refine ⟨18495376606949405217460013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49321004285198413913226701 18495376606949405217460013)
                ·
                  refine ⟨6935766227606026956547505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18495376606949405217460013 6935766227606026956547505)
                  ·
                    refine ⟨5201824670704520217410629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6935766227606026956547505 5201824670704520217410629)
                    ·
                      refine ⟨975342125757097540764493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5201824670704520217410629 975342125757097540764493)
                      ·
                        rfl

theorem cell23_1899472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_1899472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899472 prefixEnd_1899472 := by exact prefixLift 1899472
  have htrace : WordTrace (prefixWord ++ tailWord_1899472) baseStart_1899472 baseEnd_1899472 := by
    simpa [prefixWord, tailWord_1899472, baseEnd_1899472] using wordTrace_append hprefix tailTrace_1899472
  have hstable : (prefixWord ++ tailWord_1899472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899472).length < 2 ^ (prefixWord ++ tailWord_1899472).sum := by decide
  have hdescent : baseEnd_1899472 < baseStart_1899472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899476 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1899476 : Nat := 118140960795 + 1899476 * 2 ^ 59
def prefixEnd_1899476 : Nat := 4983230072969 + 3 ^ 40 * 1899476 * 2
def baseEnd_1899476 : Nat := 975344179679715525114475

theorem tailTrace_1899476 : CollatzResearch.WordTrace tailWord_1899476 prefixEnd_1899476 975344179679715525114475 := by
  unfold tailWord_1899476
  simp only [CollatzResearch.WordTrace]
  refine ⟨34639790633265165759367141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46186387511020221012489521 34639790633265165759367141)
  ·
    refine ⟨6494960743737218579881339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34639790633265165759367141 6494960743737218579881339)
    ·
      refine ⟨9742441115605827869822009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494960743737218579881339 9742441115605827869822009)
      ·
        refine ⟨7306830836704370902366507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9742441115605827869822009 7306830836704370902366507)
        ·
          refine ⟨10960246255056556353549761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306830836704370902366507 10960246255056556353549761)
          ·
            refine ⟨8220184691292417265162321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10960246255056556353549761 8220184691292417265162321)
            ·
              refine ⟨6165138518469312948871741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8220184691292417265162321 6165138518469312948871741)
              ·
                refine ⟨2311926944425992355826903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6165138518469312948871741 2311926944425992355826903)
                ·
                  refine ⟨3467890416638988533740355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311926944425992355826903 3467890416638988533740355)
                  ·
                    refine ⟨5201835624958482800610533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3467890416638988533740355 5201835624958482800610533)
                    ·
                      refine ⟨975344179679715525114475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5201835624958482800610533 975344179679715525114475)
                      ·
                        rfl

theorem cell23_1899476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1899476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899476 prefixEnd_1899476 := by exact prefixLift 1899476
  have htrace : WordTrace (prefixWord ++ tailWord_1899476) baseStart_1899476 baseEnd_1899476 := by
    simpa [prefixWord, tailWord_1899476, baseEnd_1899476] using wordTrace_append hprefix tailTrace_1899476
  have hstable : (prefixWord ++ tailWord_1899476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899476).length < 2 ^ (prefixWord ++ tailWord_1899476).sum := by decide
  have hdescent : baseEnd_1899476 < baseStart_1899476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899482 : List Nat := [3, 1, 1, 2, 4, 1, 11]
def baseStart_1899482 : Nat := 118140960795 + 1899482 * 2 ^ 59
def prefixEnd_1899482 : Nat := 4983230072969 + 3 ^ 40 * 1899482 * 2
def baseEnd_1899482 : Nat := 12041324204489413600487

theorem tailTrace_1899482 : CollatzResearch.WordTrace tailWord_1899482 prefixEnd_1899482 12041324204489413600487 := by
  unfold tailWord_1899482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319950026127148635863175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46186533403005729695635133 17319950026127148635863175)
  ·
    refine ⟨25979925039190722953794763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17319950026127148635863175 25979925039190722953794763)
    ·
      refine ⟨38969887558786084430692145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25979925039190722953794763 38969887558786084430692145)
      ·
        refine ⟨29227415669089563323019109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38969887558786084430692145 29227415669089563323019109)
        ·
          refine ⟨5480140437954293123066083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29227415669089563323019109 5480140437954293123066083)
          ·
            refine ⟨8220210656931439684599125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480140437954293123066083 8220210656931439684599125)
            ·
              refine ⟨12041324204489413600487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8220210656931439684599125 12041324204489413600487)
              ·
                rfl

theorem cell23_1899482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 11].length) (baseStart_1899482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899482 prefixEnd_1899482 := by exact prefixLift 1899482
  have htrace : WordTrace (prefixWord ++ tailWord_1899482) baseStart_1899482 baseEnd_1899482 := by
    simpa [prefixWord, tailWord_1899482, baseEnd_1899482] using wordTrace_append hprefix tailTrace_1899482
  have hstable : (prefixWord ++ tailWord_1899482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899482).length < 2 ^ (prefixWord ++ tailWord_1899482).sum := by decide
  have hdescent : baseEnd_1899482 < baseStart_1899482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899503 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 2, 4]
def baseStart_1899503 : Nat := 118140960795 + 1899503 * 2 ^ 59
def prefixEnd_1899503 : Nat := 4983230072969 + 3 ^ 40 * 1899503 * 2
def baseEnd_1899503 : Nat := 325119347885795639825617

theorem tailTrace_1899503 : CollatzResearch.WordTrace tailWord_1899503 prefixEnd_1899503 325119347885795639825617 := by
  unfold tailWord_1899503
  simp only [CollatzResearch.WordTrace]
  refine ⟨69280566037432515129967163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46187044024955010086644775 69280566037432515129967163)
  ·
    refine ⟨103920849056148772694950745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69280566037432515129967163 103920849056148772694950745)
    ·
      refine ⟨77940636792111579521213059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103920849056148772694950745 77940636792111579521213059)
      ·
        refine ⟨116910955188167369281819589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77940636792111579521213059 116910955188167369281819589)
        ·
          refine ⟨21920804097781381740341173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116910955188167369281819589 21920804097781381740341173)
          ·
            refine ⟨2055075384167004538156985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21920804097781381740341173 2055075384167004538156985)
            ·
              refine ⟨1541306538125253403617739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055075384167004538156985 1541306538125253403617739)
              ·
                refine ⟨2311959807187880105426609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541306538125253403617739 2311959807187880105426609)
                ·
                  refine ⟨1733969855390910079069957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2311959807187880105426609 1733969855390910079069957)
                  ·
                    refine ⟨325119347885795639825617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1733969855390910079069957 325119347885795639825617)
                    ·
                      rfl

theorem cell23_1899503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_1899503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899503 prefixEnd_1899503 := by exact prefixLift 1899503
  have htrace : WordTrace (prefixWord ++ tailWord_1899503) baseStart_1899503 baseEnd_1899503 := by
    simpa [prefixWord, tailWord_1899503, baseEnd_1899503] using wordTrace_append hprefix tailTrace_1899503
  have hstable : (prefixWord ++ tailWord_1899503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899503).length < 2 ^ (prefixWord ++ tailWord_1899503).sum := by decide
  have hdescent : baseEnd_1899503 < baseStart_1899503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899538 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1899538 : Nat := 118140960795 + 1899538 * 2 ^ 59
def prefixEnd_1899538 : Nat := 4983230072969 + 3 ^ 40 * 1899538 * 2
def baseEnd_1899538 : Nat := 975376015480294282539191

theorem tailTrace_1899538 : CollatzResearch.WordTrace tailWord_1899538 prefixEnd_1899538 975376015480294282539191 := by
  unfold tailWord_1899538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17320460648076429026872817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46187895061537144071660845 17320460648076429026872817)
  ·
    refine ⟨12990345486057321770154613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17320460648076429026872817 12990345486057321770154613)
    ·
      refine ⟨1217844889317873915951995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12990345486057321770154613 1217844889317873915951995)
      ·
        refine ⟨1826767333976810873927993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217844889317873915951995 1826767333976810873927993)
        ·
          refine ⟨1370075500482608155445995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1826767333976810873927993 1370075500482608155445995)
          ·
            refine ⟨2055113250723912233168993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370075500482608155445995 2055113250723912233168993)
            ·
              refine ⟨1541334938042934174876745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055113250723912233168993 1541334938042934174876745)
              ·
                refine ⟨1156001203532200631157559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541334938042934174876745 1156001203532200631157559)
                ·
                  refine ⟨1734001805298300946736339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156001203532200631157559 1734001805298300946736339)
                  ·
                    refine ⟨2601002707947451420104509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734001805298300946736339 2601002707947451420104509)
                    ·
                      refine ⟨975376015480294282539191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601002707947451420104509 975376015480294282539191)
                      ·
                        rfl

theorem cell23_1899538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1899538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899538 prefixEnd_1899538 := by exact prefixLift 1899538
  have htrace : WordTrace (prefixWord ++ tailWord_1899538) baseStart_1899538 baseEnd_1899538 := by
    simpa [prefixWord, tailWord_1899538, baseEnd_1899538] using wordTrace_append hprefix tailTrace_1899538
  have hstable : (prefixWord ++ tailWord_1899538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899538).length < 2 ^ (prefixWord ++ tailWord_1899538).sum := by decide
  have hdescent : baseEnd_1899538 < baseStart_1899538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899543 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1899543 : Nat := 118140960795 + 1899543 * 2 ^ 59
def prefixEnd_1899543 : Nat := 4983230072969 + 3 ^ 40 * 1899543 * 2
def baseEnd_1899543 : Nat := 975378582883566762976667

theorem tailTrace_1899543 : CollatzResearch.WordTrace tailWord_1899543 prefixEnd_1899543 975378582883566762976667 := by
  unfold tailWord_1899543
  simp only [CollatzResearch.WordTrace]
  refine ⟨69282024957287601961423283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46188016638191734640948855 69282024957287601961423283)
  ·
    refine ⟨103923037435931402942134925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69282024957287601961423283 103923037435931402942134925)
    ·
      refine ⟨38971139038474276103300597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103923037435931402942134925 38971139038474276103300597)
      ·
        refine ⟨3653544284856963384684431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38971139038474276103300597 3653544284856963384684431)
        ·
          refine ⟨5480316427285445077026647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653544284856963384684431 5480316427285445077026647)
          ·
            refine ⟨8220474640928167615539971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480316427285445077026647 8220474640928167615539971)
            ·
              refine ⟨12330711961392251423309957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8220474640928167615539971 12330711961392251423309957)
              ·
                refine ⟨2312008492761047141870617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12330711961392251423309957 2312008492761047141870617)
                ·
                  refine ⟨1734006369570785356402963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312008492761047141870617 1734006369570785356402963)
                  ·
                    refine ⟨2601009554356178034604445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734006369570785356402963 2601009554356178034604445)
                    ·
                      refine ⟨975378582883566762976667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601009554356178034604445 975378582883566762976667)
                      ·
                        rfl

theorem cell23_1899543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1899543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899543 prefixEnd_1899543 := by exact prefixLift 1899543
  have htrace : WordTrace (prefixWord ++ tailWord_1899543) baseStart_1899543 baseEnd_1899543 := by
    simpa [prefixWord, tailWord_1899543, baseEnd_1899543] using wordTrace_append hprefix tailTrace_1899543
  have hstable : (prefixWord ++ tailWord_1899543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899543).length < 2 ^ (prefixWord ++ tailWord_1899543).sum := by decide
  have hdescent : baseEnd_1899543 < baseStart_1899543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899569 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1899569 : Nat := 118140960795 + 1899569 * 2 ^ 59
def prefixEnd_1899569 : Nat := 4983230072969 + 3 ^ 40 * 1899569 * 2
def baseEnd_1899569 : Nat := 975391933380583661251547

theorem tailTrace_1899569 : CollatzResearch.WordTrace tailWord_1899569 prefixEnd_1899569 975391933380583661251547 := by
  unfold tailWord_1899569
  simp only [CollatzResearch.WordTrace]
  refine ⟨69282973255193408401869761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46188648836795605601246507 69282973255193408401869761)
  ·
    refine ⟨51962229941395056301402321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69282973255193408401869761 51962229941395056301402321)
    ·
      refine ⟨38971672456046292226051741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51962229941395056301402321 38971672456046292226051741)
      ·
        refine ⟨14614377171017359584769403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38971672456046292226051741 14614377171017359584769403)
        ·
          refine ⟨21921565756526039377154105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14614377171017359584769403 21921565756526039377154105)
          ·
            refine ⟨16441174317394529532865579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21921565756526039377154105 16441174317394529532865579)
            ·
              refine ⟨24661761476091794299298369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441174317394529532865579 24661761476091794299298369)
              ·
                refine ⟨18496321107068845724473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24661761476091794299298369 18496321107068845724473777)
                ·
                  refine ⟨13872240830301634293355333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18496321107068845724473777 13872240830301634293355333)
                  ·
                    refine ⟨2601045155681556430004125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13872240830301634293355333 2601045155681556430004125)
                    ·
                      refine ⟨975391933380583661251547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601045155681556430004125 975391933380583661251547)
                      ·
                        rfl

theorem cell23_1899569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1899569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899569 prefixEnd_1899569 := by exact prefixLift 1899569
  have htrace : WordTrace (prefixWord ++ tailWord_1899569) baseStart_1899569 baseEnd_1899569 := by
    simpa [prefixWord, tailWord_1899569, baseEnd_1899569] using wordTrace_append hprefix tailTrace_1899569
  have hstable : (prefixWord ++ tailWord_1899569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899569).length < 2 ^ (prefixWord ++ tailWord_1899569).sum := by decide
  have hdescent : baseEnd_1899569 < baseStart_1899569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899639 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1899639 : Nat := 118140960795 + 1899639 * 2 ^ 59
def prefixEnd_1899639 : Nat := 4983230072969 + 3 ^ 40 * 1899639 * 2
def baseEnd_1899639 : Nat := 975427877026398387376225

theorem tailTrace_1899639 : CollatzResearch.WordTrace tailWord_1899639 prefixEnd_1899639 975427877026398387376225 := by
  unfold tailWord_1899639
  simp only [CollatzResearch.WordTrace]
  refine ⟨69285526364939810356917971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46190350909959873571278647 69285526364939810356917971)
  ·
    refine ⟨103928289547409715535376957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69285526364939810356917971 103928289547409715535376957)
    ·
      refine ⟨38973108580278643325766359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103928289547409715535376957 38973108580278643325766359)
      ·
        refine ⟨58459662870417964988649539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38973108580278643325766359 58459662870417964988649539)
        ·
          refine ⟨87689494305626947482974309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58459662870417964988649539 87689494305626947482974309)
          ·
            refine ⟨16441780182305052653057683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87689494305626947482974309 16441780182305052653057683)
            ·
              refine ⟨24662670273457578979586525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16441780182305052653057683 24662670273457578979586525)
              ·
                refine ⟨9248501352546592117344947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24662670273457578979586525 9248501352546592117344947)
                ·
                  refine ⟨13872752028819888176017421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9248501352546592117344947 13872752028819888176017421)
                  ·
                    refine ⟨5202282010807458066006533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13872752028819888176017421 5202282010807458066006533)
                    ·
                      refine ⟨975427877026398387376225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5202282010807458066006533 975427877026398387376225)
                      ·
                        rfl

theorem cell23_1899639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1899639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899639 prefixEnd_1899639 := by exact prefixLift 1899639
  have htrace : WordTrace (prefixWord ++ tailWord_1899639) baseStart_1899639 baseEnd_1899639 := by
    simpa [prefixWord, tailWord_1899639, baseEnd_1899639] using wordTrace_append hprefix tailTrace_1899639
  have hstable : (prefixWord ++ tailWord_1899639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899639).length < 2 ^ (prefixWord ++ tailWord_1899639).sum := by decide
  have hdescent : baseEnd_1899639 < baseStart_1899639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899669 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1899669 : Nat := 118140960795 + 1899669 * 2 ^ 59
def prefixEnd_1899669 : Nat := 4983230072969 + 3 ^ 40 * 1899669 * 2
def baseEnd_1899669 : Nat := 975443281446033270001087

theorem tailTrace_1899669 : CollatzResearch.WordTrace tailWord_1899669 prefixEnd_1899669 975443281446033270001087 := by
  unfold tailWord_1899669
  simp only [CollatzResearch.WordTrace]
  refine ⟨69286620554831125480510061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46191080369887416987006707 69286620554831125480510061)
  ·
    refine ⟨25982482708061672055191273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69286620554831125480510061 25982482708061672055191273)
    ·
      refine ⟨19486862031046254041393455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25982482708061672055191273 19486862031046254041393455)
      ·
        refine ⟨29230293046569381062090183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19486862031046254041393455 29230293046569381062090183)
        ·
          refine ⟨43845439569854071593135275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29230293046569381062090183 43845439569854071593135275)
          ·
            refine ⟨65768159354781107389702913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43845439569854071593135275 65768159354781107389702913)
            ·
              refine ⟨49326119516085830542277185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65768159354781107389702913 49326119516085830542277185)
              ·
                refine ⟨36994589637064372906707889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49326119516085830542277185 36994589637064372906707889)
                ·
                  refine ⟨27745942227798279680030917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36994589637064372906707889 27745942227798279680030917)
                  ·
                    refine ⟨5202364167712177440005797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27745942227798279680030917 5202364167712177440005797)
                    ·
                      refine ⟨975443281446033270001087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5202364167712177440005797 975443281446033270001087)
                      ·
                        rfl

theorem cell23_1899669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1899669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899669 prefixEnd_1899669 := by exact prefixLift 1899669
  have htrace : WordTrace (prefixWord ++ tailWord_1899669) baseStart_1899669 baseEnd_1899669 := by
    simpa [prefixWord, tailWord_1899669, baseEnd_1899669] using wordTrace_append hprefix tailTrace_1899669
  have hstable : (prefixWord ++ tailWord_1899669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899669).length < 2 ^ (prefixWord ++ tailWord_1899669).sum := by decide
  have hdescent : baseEnd_1899669 < baseStart_1899669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899690 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1899690 : Nat := 118140960795 + 1899690 * 2 ^ 59
def prefixEnd_1899690 : Nat := 4983230072969 + 3 ^ 40 * 1899690 * 2
def baseEnd_1899690 : Nat := 975454064539777687838491

theorem tailTrace_1899690 : CollatzResearch.WordTrace tailWord_1899690 prefixEnd_1899690 975454064539777687838491 := by
  unfold tailWord_1899690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321846621938761516756131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46191590991836697378016349 17321846621938761516756131)
  ·
    refine ⟨25982769932908142275134197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17321846621938761516756131 25982769932908142275134197)
    ·
      refine ⟨2435884681210138338293831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25982769932908142275134197 2435884681210138338293831)
      ·
        refine ⟨3653827021815207507440747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435884681210138338293831 3653827021815207507440747)
        ·
          refine ⟨5480740532722811261161121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653827021815207507440747 5480740532722811261161121)
          ·
            refine ⟨4110555399542108445870841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5480740532722811261161121 4110555399542108445870841)
            ·
              refine ⟨3082916549656581334403131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110555399542108445870841 3082916549656581334403131)
              ·
                refine ⟨4624374824484872001604697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082916549656581334403131 4624374824484872001604697)
                ·
                  refine ⟨3468281118363654001203523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624374824484872001604697 3468281118363654001203523)
                  ·
                    refine ⟨5202421677545481001805285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468281118363654001203523 5202421677545481001805285)
                    ·
                      refine ⟨975454064539777687838491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5202421677545481001805285 975454064539777687838491)
                      ·
                        rfl

theorem cell23_1899690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1899690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899690 prefixEnd_1899690 := by exact prefixLift 1899690
  have htrace : WordTrace (prefixWord ++ tailWord_1899690) baseStart_1899690 baseEnd_1899690 := by
    simpa [prefixWord, tailWord_1899690, baseEnd_1899690] using wordTrace_append hprefix tailTrace_1899690
  have hstable : (prefixWord ++ tailWord_1899690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899690).length < 2 ^ (prefixWord ++ tailWord_1899690).sum := by decide
  have hdescent : baseEnd_1899690 < baseStart_1899690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899713 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 6]
def baseStart_1899713 : Nat := 118140960795 + 1899713 * 2 ^ 59
def prefixEnd_1899713 : Nat := 4983230072969 + 3 ^ 40 * 1899713 * 2
def baseEnd_1899713 : Nat := 108385097177203455316765

theorem tailTrace_1899713 : CollatzResearch.WordTrace tailWord_1899713 prefixEnd_1899713 108385097177203455316765 := by
  unfold tailWord_1899713
  simp only [CollatzResearch.WordTrace]
  refine ⟨69288225366671720995111793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46192150244447813996741195 69288225366671720995111793)
  ·
    refine ⟨51966169025003790746333845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69288225366671720995111793 51966169025003790746333845)
    ·
      refine ⟨2435914173047052691234399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51966169025003790746333845 2435914173047052691234399)
      ·
        refine ⟨3653871259570579036851599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435914173047052691234399 3653871259570579036851599)
        ·
          refine ⟨5480806889355868555277399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653871259570579036851599 5480806889355868555277399)
          ·
            refine ⟨8221210334033802832916099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480806889355868555277399 8221210334033802832916099)
            ·
              refine ⟨12331815501050704249374149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221210334033802832916099 12331815501050704249374149)
              ·
                refine ⟨2312215406447007046757653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12331815501050704249374149 2312215406447007046757653)
                ·
                  refine ⟨108385097177203455316765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2312215406447007046757653 108385097177203455316765)
                  ·
                    rfl

theorem cell23_1899713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_1899713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899713 prefixEnd_1899713 := by exact prefixLift 1899713
  have htrace : WordTrace (prefixWord ++ tailWord_1899713) baseStart_1899713 baseEnd_1899713 := by
    simpa [prefixWord, tailWord_1899713, baseEnd_1899713] using wordTrace_append hprefix tailTrace_1899713
  have hstable : (prefixWord ++ tailWord_1899713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899713).length < 2 ^ (prefixWord ++ tailWord_1899713).sum := by decide
  have hdescent : baseEnd_1899713 < baseStart_1899713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899719 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1899719 : Nat := 118140960795 + 1899719 * 2 ^ 59
def prefixEnd_1899719 : Nat := 4983230072969 + 3 ^ 40 * 1899719 * 2
def baseEnd_1899719 : Nat := 975468955478758074375857

theorem tailTrace_1899719 : CollatzResearch.WordTrace tailWord_1899719 prefixEnd_1899719 975468955478758074375857 := by
  unfold tailWord_1899719
  simp only [CollatzResearch.WordTrace]
  refine ⟨69288444204649984019830211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46192296136433322679886807 69288444204649984019830211)
  ·
    refine ⟨103932666306974976029745317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69288444204649984019830211 103932666306974976029745317)
    ·
      refine ⟨19487374932557808005577247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103932666306974976029745317 19487374932557808005577247)
      ·
        refine ⟨29231062398836712008365871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19487374932557808005577247 29231062398836712008365871)
        ·
          refine ⟨43846593598255068012548807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29231062398836712008365871 43846593598255068012548807)
          ·
            refine ⟨65769890397382602018823211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43846593598255068012548807 65769890397382602018823211)
            ·
              refine ⟨98654835596073903028234817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65769890397382602018823211 98654835596073903028234817)
              ·
                refine ⟨73991126697055427271176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98654835596073903028234817 73991126697055427271176113)
                ·
                  refine ⟨55493345022791570453382085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73991126697055427271176113 55493345022791570453382085)
                  ·
                    refine ⟨10405002191773419460009141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55493345022791570453382085 10405002191773419460009141)
                    ·
                      refine ⟨975468955478758074375857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10405002191773419460009141 975468955478758074375857)
                      ·
                        rfl

theorem cell23_1899719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1899719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899719 prefixEnd_1899719 := by exact prefixLift 1899719
  have htrace : WordTrace (prefixWord ++ tailWord_1899719) baseStart_1899719 baseEnd_1899719 := by
    simpa [prefixWord, tailWord_1899719, baseEnd_1899719] using wordTrace_append hprefix tailTrace_1899719
  have hstable : (prefixWord ++ tailWord_1899719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899719).length < 2 ^ (prefixWord ++ tailWord_1899719).sum := by decide
  have hdescent : baseEnd_1899719 < baseStart_1899719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899756 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_1899756 : Nat := 118140960795 + 1899756 * 2 ^ 59
def prefixEnd_1899756 : Nat := 4983230072969 + 3 ^ 40 * 1899756 * 2
def baseEnd_1899756 : Nat := 325162651420991476537729

theorem tailTrace_1899756 : CollatzResearch.WordTrace tailWord_1899756 prefixEnd_1899756 325162651420991476537729 := by
  unfold tailWord_1899756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34644896852757969669463561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46193195803677292892618081 34644896852757969669463561)
  ·
    refine ⟨25983672639568477252097671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34644896852757969669463561 25983672639568477252097671)
    ·
      refine ⟨38975508959352715878146507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25983672639568477252097671 38975508959352715878146507)
      ·
        refine ⟨58463263439029073817219761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38975508959352715878146507 58463263439029073817219761)
        ·
          refine ⟨43847447579271805362914821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58463263439029073817219761 43847447579271805362914821)
          ·
            refine ⟨8221396421113463505546529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43847447579271805362914821 8221396421113463505546529)
            ·
              refine ⟨6166047315835097629159897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8221396421113463505546529 6166047315835097629159897)
              ·
                refine ⟨4624535486876323221869923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166047315835097629159897 4624535486876323221869923)
                ·
                  refine ⟨6936803230314484832804885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624535486876323221869923 6936803230314484832804885)
                  ·
                    refine ⟨325162651420991476537729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6936803230314484832804885 325162651420991476537729)
                    ·
                      rfl

theorem cell23_1899756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_1899756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899756 prefixEnd_1899756 := by exact prefixLift 1899756
  have htrace : WordTrace (prefixWord ++ tailWord_1899756) baseStart_1899756 baseEnd_1899756 := by
    simpa [prefixWord, tailWord_1899756, baseEnd_1899756] using wordTrace_append hprefix tailTrace_1899756
  have hstable : (prefixWord ++ tailWord_1899756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899756).length < 2 ^ (prefixWord ++ tailWord_1899756).sum := by decide
  have hdescent : baseEnd_1899756 < baseStart_1899756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899757 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1899757 : Nat := 118140960795 + 1899757 * 2 ^ 59
def prefixEnd_1899757 : Nat := 4983230072969 + 3 ^ 40 * 1899757 * 2
def baseEnd_1899757 : Nat := 975488467743628925700683

theorem tailTrace_1899757 : CollatzResearch.WordTrace tailWord_1899757 prefixEnd_1899757 975488467743628925700683 := by
  unfold tailWord_1899757
  simp only [CollatzResearch.WordTrace]
  refine ⟨69289830178512316509713525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46193220119008211006475683 69289830178512316509713525)
  ·
    refine ⟨6495921579235529672785643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69289830178512316509713525 6495921579235529672785643)
    ·
      refine ⟨9743882368853294509178465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6495921579235529672785643 9743882368853294509178465)
      ·
        refine ⟨7307911776639970881883849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9743882368853294509178465 7307911776639970881883849)
        ·
          refine ⟨5480933832479978161412887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7307911776639970881883849 5480933832479978161412887)
          ·
            refine ⟨8221400748719967242119331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480933832479978161412887 8221400748719967242119331)
            ·
              refine ⟨12332101123079950863178997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221400748719967242119331 12332101123079950863178997)
              ·
                refine ⟨1156134480288745393423031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12332101123079950863178997 1156134480288745393423031)
                ·
                  refine ⟨1734201720433118090134547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156134480288745393423031 1734201720433118090134547)
                  ·
                    refine ⟨2601302580649677135201821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734201720433118090134547 2601302580649677135201821)
                    ·
                      refine ⟨975488467743628925700683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601302580649677135201821 975488467743628925700683)
                      ·
                        rfl

theorem cell23_1899757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1899757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899757 prefixEnd_1899757 := by exact prefixLift 1899757
  have htrace : WordTrace (prefixWord ++ tailWord_1899757) baseStart_1899757 baseEnd_1899757 := by
    simpa [prefixWord, tailWord_1899757, baseEnd_1899757] using wordTrace_append hprefix tailTrace_1899757
  have hstable : (prefixWord ++ tailWord_1899757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899757).length < 2 ^ (prefixWord ++ tailWord_1899757).sum := by decide
  have hdescent : baseEnd_1899757 < baseStart_1899757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899763 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 4]
def baseStart_1899763 : Nat := 118140960795 + 1899763 * 2 ^ 59
def prefixEnd_1899763 : Nat := 4983230072969 + 3 ^ 40 * 1899763 * 2
def baseEnd_1899763 : Nat := 975491548627555902225655

theorem tailTrace_1899763 : CollatzResearch.WordTrace tailWord_1899763 prefixEnd_1899763 975491548627555902225655 := by
  unfold tailWord_1899763
  simp only [CollatzResearch.WordTrace]
  refine ⟨69290049016490579534431943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46193366010993719689621295 69290049016490579534431943)
  ·
    refine ⟨103935073524735869301647915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69290049016490579534431943 103935073524735869301647915)
    ·
      refine ⟨155902610287103803952471873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103935073524735869301647915 155902610287103803952471873)
      ·
        refine ⟨116926957715327852964353905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155902610287103803952471873 116926957715327852964353905)
        ·
          refine ⟨87695218286495889723265429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116926957715327852964353905 87695218286495889723265429)
          ·
            refine ⟨4110713357179494830778067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87695218286495889723265429 4110713357179494830778067)
            ·
              refine ⟨6166070035769242246167101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110713357179494830778067 6166070035769242246167101)
              ·
                refine ⟨2312276263413465842312663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6166070035769242246167101 2312276263413465842312663)
                ·
                  refine ⟨3468414395120198763468995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312276263413465842312663 3468414395120198763468995)
                  ·
                    refine ⟨5202621592680298145203493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3468414395120198763468995 5202621592680298145203493)
                    ·
                      refine ⟨975491548627555902225655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5202621592680298145203493 975491548627555902225655)
                      ·
                        rfl

theorem cell23_1899763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 4].length) (baseStart_1899763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899763 prefixEnd_1899763 := by exact prefixLift 1899763
  have htrace : WordTrace (prefixWord ++ tailWord_1899763) baseStart_1899763 baseEnd_1899763 := by
    simpa [prefixWord, tailWord_1899763, baseEnd_1899763] using wordTrace_append hprefix tailTrace_1899763
  have hstable : (prefixWord ++ tailWord_1899763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899763).length < 2 ^ (prefixWord ++ tailWord_1899763).sum := by decide
  have hdescent : baseEnd_1899763 < baseStart_1899763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899764 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1899764 : Nat := 118140960795 + 1899764 * 2 ^ 59
def prefixEnd_1899764 : Nat := 4983230072969 + 3 ^ 40 * 1899764 * 2
def baseEnd_1899764 : Nat := 108388006900912266479239

theorem tailTrace_1899764 : CollatzResearch.WordTrace tailWord_1899764 prefixEnd_1899764 108388006900912266479239 := by
  unfold tailWord_1899764
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645042744743478352609173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46193390326324637803478897 34645042744743478352609173)
  ·
    refine ⟨1623986378659850547778555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34645042744743478352609173 1623986378659850547778555)
    ·
      refine ⟨2435979567989775821667833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623986378659850547778555 2435979567989775821667833)
      ·
        refine ⟨1826984675992331866250875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2435979567989775821667833 1826984675992331866250875)
        ·
          refine ⟨2740477013988497799376313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826984675992331866250875 2740477013988497799376313)
          ·
            refine ⟨2055357760491373349532235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740477013988497799376313 2055357760491373349532235)
            ·
              refine ⟨3083036640737060024298353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055357760491373349532235 3083036640737060024298353)
              ·
                refine ⟨2312277480552795018223765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083036640737060024298353 2312277480552795018223765)
                ·
                  refine ⟨108388006900912266479239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2312277480552795018223765 108388006900912266479239)
                  ·
                    rfl

theorem cell23_1899764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1899764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899764 prefixEnd_1899764 := by exact prefixLift 1899764
  have htrace : WordTrace (prefixWord ++ tailWord_1899764) baseStart_1899764 baseEnd_1899764 := by
    simpa [prefixWord, tailWord_1899764, baseEnd_1899764] using wordTrace_append hprefix tailTrace_1899764
  have hstable : (prefixWord ++ tailWord_1899764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899764).length < 2 ^ (prefixWord ++ tailWord_1899764).sum := by decide
  have hdescent : baseEnd_1899764 < baseStart_1899764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899769 : List Nat := [1, 2, 1, 3, 1, 1, 14]
def baseStart_1899769 : Nat := 118140960795 + 1899769 * 2 ^ 59
def prefixEnd_1899769 : Nat := 4983230072969 + 3 ^ 40 * 1899769 * 2
def baseEnd_1899769 : Nat := 12043143574215838009267

theorem tailTrace_1899769 : CollatzResearch.WordTrace tailWord_1899769 prefixEnd_1899769 12043143574215838009267 := by
  unfold tailWord_1899769
  simp only [CollatzResearch.WordTrace]
  refine ⟨69290267854468842559150361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46193511902979228372766907 69290267854468842559150361)
  ·
    refine ⟨51967700890851631919362771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69290267854468842559150361 51967700890851631919362771)
    ·
      refine ⟨77951551336277447879044157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51967700890851631919362771 77951551336277447879044157)
      ·
        refine ⟨29231831751104042954641559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77951551336277447879044157 29231831751104042954641559)
        ·
          refine ⟨43847747626656064431962339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29231831751104042954641559 43847747626656064431962339)
          ·
            refine ⟨65771621439984096647943509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43847747626656064431962339 65771621439984096647943509)
            ·
              refine ⟨12043143574215838009267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 65771621439984096647943509 12043143574215838009267)
              ·
                rfl

theorem cell23_1899769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 14].length) (baseStart_1899769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899769 prefixEnd_1899769 := by exact prefixLift 1899769
  have htrace : WordTrace (prefixWord ++ tailWord_1899769) baseStart_1899769 baseEnd_1899769 := by
    simpa [prefixWord, tailWord_1899769, baseEnd_1899769] using wordTrace_append hprefix tailTrace_1899769
  have hstable : (prefixWord ++ tailWord_1899769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899769).length < 2 ^ (prefixWord ++ tailWord_1899769).sum := by decide
  have hdescent : baseEnd_1899769 < baseStart_1899769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899800 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1899800 : Nat := 118140960795 + 1899800 * 2 ^ 59
def prefixEnd_1899800 : Nat := 4983230072969 + 3 ^ 40 * 1899800 * 2
def baseEnd_1899800 : Nat := 975510547411772257462985

theorem tailTrace_1899800 : CollatzResearch.WordTrace tailWord_1899800 prefixEnd_1899800 975510547411772257462985 := by
  unfold tailWord_1899800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645699258678267426764427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46194265678237689902352569 34645699258678267426764427)
  ·
    refine ⟨51968548888017401140146641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34645699258678267426764427 51968548888017401140146641)
    ·
      refine ⟨38976411666013050855109981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51968548888017401140146641 38976411666013050855109981)
      ·
        refine ⟨14616154374754894070666243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38976411666013050855109981 14616154374754894070666243)
        ·
          refine ⟨21924231562132341105999365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14616154374754894070666243 21924231562132341105999365)
          ·
            refine ⟨4110793417899813957374881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21924231562132341105999365 4110793417899813957374881)
            ·
              refine ⟨3083095063424860468031161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110793417899813957374881 3083095063424860468031161)
              ·
                refine ⟨2312321297568645351023371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083095063424860468031161 2312321297568645351023371)
                ·
                  refine ⟨3468481946352968026535057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312321297568645351023371 3468481946352968026535057)
                  ·
                    refine ⟨2601361459764726019901293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3468481946352968026535057 2601361459764726019901293)
                    ·
                      refine ⟨975510547411772257462985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601361459764726019901293 975510547411772257462985)
                      ·
                        rfl

theorem cell23_1899800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1899800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899800 prefixEnd_1899800 := by exact prefixLift 1899800
  have htrace : WordTrace (prefixWord ++ tailWord_1899800) baseStart_1899800 baseEnd_1899800 := by
    simpa [prefixWord, tailWord_1899800, baseEnd_1899800] using wordTrace_append hprefix tailTrace_1899800
  have hstable : (prefixWord ++ tailWord_1899800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899800).length < 2 ^ (prefixWord ++ tailWord_1899800).sum := by decide
  have hdescent : baseEnd_1899800 < baseStart_1899800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899823 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 5, 3, 2]
def baseStart_1899823 : Nat := 118140960795 + 1899823 * 2 ^ 59
def prefixEnd_1899823 : Nat := 4983230072969 + 3 ^ 40 * 1899823 * 2
def baseEnd_1899823 : Nat := 975522357466825667475379

theorem tailTrace_1899823 : CollatzResearch.WordTrace tailWord_1899823 prefixEnd_1899823 975522357466825667475379 := by
  unfold tailWord_1899823
  simp only [CollatzResearch.WordTrace]
  refine ⟨69292237396273209781616123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46194824930848806521077415 69292237396273209781616123)
  ·
    refine ⟨103938356094409814672424185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69292237396273209781616123 103938356094409814672424185)
    ·
      refine ⟨77953767070807361004318139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103938356094409814672424185 77953767070807361004318139)
      ·
        refine ⟨116930650606211041506477209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77953767070807361004318139 116930650606211041506477209)
        ·
          refine ⟨87697987954658281129857907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116930650606211041506477209 87697987954658281129857907)
          ·
            refine ⟨131546981931987421694786861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87697987954658281129857907 131546981931987421694786861)
            ·
              refine ⟨49330118224495283135545073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131546981931987421694786861 49330118224495283135545073)
              ·
                refine ⟨36997588668371462351658805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49330118224495283135545073 36997588668371462351658805)
                ·
                  refine ⟨3468523937659824595468013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36997588668371462351658805 3468523937659824595468013)
                  ·
                    refine ⟨1300696476622434223300505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468523937659824595468013 1300696476622434223300505)
                    ·
                      refine ⟨975522357466825667475379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300696476622434223300505 975522357466825667475379)
                      ·
                        rfl

theorem cell23_1899823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3, 2].length) (baseStart_1899823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899823 prefixEnd_1899823 := by exact prefixLift 1899823
  have htrace : WordTrace (prefixWord ++ tailWord_1899823) baseStart_1899823 baseEnd_1899823 := by
    simpa [prefixWord, tailWord_1899823, baseEnd_1899823] using wordTrace_append hprefix tailTrace_1899823
  have hstable : (prefixWord ++ tailWord_1899823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899823).length < 2 ^ (prefixWord ++ tailWord_1899823).sum := by decide
  have hdescent : baseEnd_1899823 < baseStart_1899823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899847 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_1899847 : Nat := 118140960795 + 1899847 * 2 ^ 59
def prefixEnd_1899847 : Nat := 4983230072969 + 3 ^ 40 * 1899847 * 2
def baseEnd_1899847 : Nat := 975534681002533573575269

theorem tailTrace_1899847 : CollatzResearch.WordTrace tailWord_1899847 prefixEnd_1899847 975534681002533573575269 := by
  unfold tailWord_1899847
  simp only [CollatzResearch.WordTrace]
  refine ⟨69293112748186261880489795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46195408498790841253659863 69293112748186261880489795)
  ·
    refine ⟨103939669122279392820734693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69293112748186261880489795 103939669122279392820734693)
    ·
      refine ⟨19488687960427386153887755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103939669122279392820734693 19488687960427386153887755)
      ·
        refine ⟨29233031940641079230831633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488687960427386153887755 29233031940641079230831633)
        ·
          refine ⟨21924773955480809423123725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29233031940641079230831633 21924773955480809423123725)
          ·
            refine ⟨8221790233305303533671397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21924773955480809423123725 8221790233305303533671397)
            ·
              refine ⟨1541585668744744412563387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8221790233305303533671397 1541585668744744412563387)
              ·
                refine ⟨2312378503117116618845081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541585668744744412563387 2312378503117116618845081)
                ·
                  refine ⟨1734283877337837464133811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312378503117116618845081 1734283877337837464133811)
                  ·
                    refine ⟨2601425816006756196200717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734283877337837464133811 2601425816006756196200717)
                    ·
                      refine ⟨975534681002533573575269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601425816006756196200717 975534681002533573575269)
                      ·
                        rfl

theorem cell23_1899847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_1899847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899847 prefixEnd_1899847 := by exact prefixLift 1899847
  have htrace : WordTrace (prefixWord ++ tailWord_1899847) baseStart_1899847 baseEnd_1899847 := by
    simpa [prefixWord, tailWord_1899847, baseEnd_1899847] using wordTrace_append hprefix tailTrace_1899847
  have hstable : (prefixWord ++ tailWord_1899847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899847).length < 2 ^ (prefixWord ++ tailWord_1899847).sum := by decide
  have hdescent : baseEnd_1899847 < baseStart_1899847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899856 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_1899856 : Nat := 118140960795 + 1899856 * 2 ^ 59
def prefixEnd_1899856 : Nat := 4983230072969 + 3 ^ 40 * 1899856 * 2
def baseEnd_1899856 : Nat := 975539302328424038362727

theorem tailTrace_1899856 : CollatzResearch.WordTrace tailWord_1899856 prefixEnd_1899856 975539302328424038362727 := by
  unfold tailWord_1899856
  simp only [CollatzResearch.WordTrace]
  refine ⟨34646720502576828208783711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46195627336769104278378281 34646720502576828208783711)
  ·
    refine ⟨51970080753865242313175567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34646720502576828208783711 51970080753865242313175567)
    ·
      refine ⟨77955121130797863469763351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51970080753865242313175567 77955121130797863469763351)
      ·
        refine ⟨116932681696196795204645027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77955121130797863469763351 116932681696196795204645027)
        ·
          refine ⟨175399022544295192806967541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116932681696196795204645027 175399022544295192806967541)
          ·
            refine ⟨16443658363527674325653207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175399022544295192806967541 16443658363527674325653207)
            ·
              refine ⟨24665487545291511488479811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16443658363527674325653207 24665487545291511488479811)
              ·
                refine ⟨36998231317937267232719717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24665487545291511488479811 36998231317937267232719717)
                ·
                  refine ⟨6937168372113237606134947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36998231317937267232719717 6937168372113237606134947)
                  ·
                    refine ⟨10405752558169856409202421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6937168372113237606134947 10405752558169856409202421)
                    ·
                      refine ⟨975539302328424038362727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10405752558169856409202421 975539302328424038362727)
                      ·
                        rfl

theorem cell23_1899856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_1899856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899856 prefixEnd_1899856 := by exact prefixLift 1899856
  have htrace : WordTrace (prefixWord ++ tailWord_1899856) baseStart_1899856 baseEnd_1899856 := by
    simpa [prefixWord, tailWord_1899856, baseEnd_1899856] using wordTrace_append hprefix tailTrace_1899856
  have hstable : (prefixWord ++ tailWord_1899856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899856).length < 2 ^ (prefixWord ++ tailWord_1899856).sum := by decide
  have hdescent : baseEnd_1899856 < baseStart_1899856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899874 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1899874 : Nat := 118140960795 + 1899874 * 2 ^ 59
def prefixEnd_1899874 : Nat := 4983230072969 + 3 ^ 40 * 1899874 * 2
def baseEnd_1899874 : Nat := 975548544980204967937645

theorem tailTrace_1899874 : CollatzResearch.WordTrace tailWord_1899874 prefixEnd_1899874 975548544980204967937645 := by
  unfold tailWord_1899874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17323524379772111372930669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46196065012725630327815117 17323524379772111372930669)
  ·
    refine ⟨6496321642414541764849001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17323524379772111372930669 6496321642414541764849001)
    ·
      refine ⟨4872241231810906323636751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6496321642414541764849001 4872241231810906323636751)
      ·
        refine ⟨7308361847716359485455127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872241231810906323636751 7308361847716359485455127)
        ·
          refine ⟨10962542771574539228182691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308361847716359485455127 10962542771574539228182691)
          ·
            refine ⟨16443814157361808842274037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10962542771574539228182691 16443814157361808842274037)
            ·
              refine ⟨1541607577252669578963191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16443814157361808842274037 1541607577252669578963191)
              ·
                refine ⟨2312411365879004368444787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541607577252669578963191 2312411365879004368444787)
                ·
                  refine ⟨3468617048818506552667181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312411365879004368444787 3468617048818506552667181)
                  ·
                    refine ⟨1300731393306939957250193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3468617048818506552667181 1300731393306939957250193)
                    ·
                      refine ⟨975548544980204967937645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300731393306939957250193 975548544980204967937645)
                      ·
                        rfl

theorem cell23_1899874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1899874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899874 prefixEnd_1899874 := by exact prefixLift 1899874
  have htrace : WordTrace (prefixWord ++ tailWord_1899874) baseStart_1899874 baseEnd_1899874 := by
    simpa [prefixWord, tailWord_1899874, baseEnd_1899874] using wordTrace_append hprefix tailTrace_1899874
  have hstable : (prefixWord ++ tailWord_1899874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899874).length < 2 ^ (prefixWord ++ tailWord_1899874).sum := by decide
  have hdescent : baseEnd_1899874 < baseStart_1899874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899887 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 2, 2, 2]
def baseStart_1899887 : Nat := 118140960795 + 1899887 * 2 ^ 59
def prefixEnd_1899887 : Nat := 4983230072969 + 3 ^ 40 * 1899887 * 2
def baseEnd_1899887 : Nat := 975555220228713417075085

theorem tailTrace_1899887 : CollatzResearch.WordTrace tailWord_1899887 prefixEnd_1899887 975555220228713417075085 := by
  unfold tailWord_1899887
  simp only [CollatzResearch.WordTrace]
  refine ⟨69294571668041348711945915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46196381112027565807963943 69294571668041348711945915)
  ·
    refine ⟨103941857502062023067918873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69294571668041348711945915 103941857502062023067918873)
    ·
      refine ⟨77956393126546517300939155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103941857502062023067918873 77956393126546517300939155)
      ·
        refine ⟨116934589689819775951408733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77956393126546517300939155 116934589689819775951408733)
        ·
          refine ⟨43850471133682415981778275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116934589689819775951408733 43850471133682415981778275)
          ·
            refine ⟨65775706700523623972667413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43850471133682415981778275 65775706700523623972667413)
            ·
              refine ⟨3083236251587044873718785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65775706700523623972667413 3083236251587044873718785)
              ·
                refine ⟨2312427188690283655289089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083236251587044873718785 2312427188690283655289089)
                ·
                  refine ⟨1734320391517712741466817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312427188690283655289089 1734320391517712741466817)
                  ·
                    refine ⟨1300740293638284556100113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1734320391517712741466817 1300740293638284556100113)
                    ·
                      refine ⟨975555220228713417075085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300740293638284556100113 975555220228713417075085)
                      ·
                        rfl

theorem cell23_1899887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 2, 2].length) (baseStart_1899887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899887 prefixEnd_1899887 := by exact prefixLift 1899887
  have htrace : WordTrace (prefixWord ++ tailWord_1899887) baseStart_1899887 baseEnd_1899887 := by
    simpa [prefixWord, tailWord_1899887, baseEnd_1899887] using wordTrace_append hprefix tailTrace_1899887
  have hstable : (prefixWord ++ tailWord_1899887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899887).length < 2 ^ (prefixWord ++ tailWord_1899887).sum := by decide
  have hdescent : baseEnd_1899887 < baseStart_1899887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899960 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2]
def baseStart_1899960 : Nat := 118140960795 + 1899960 * 2 ^ 59
def prefixEnd_1899960 : Nat := 4983230072969 + 3 ^ 40 * 1899960 * 2
def baseEnd_1899960 : Nat := 975592704316491631462249

theorem tailTrace_1899960 : CollatzResearch.WordTrace tailWord_1899960 prefixEnd_1899960 975592704316491631462249 := by
  unfold tailWord_1899960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34648617098388441089676667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46198156131184588119568889 34648617098388441089676667)
  ·
    refine ⟨51972925647582661634515001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34648617098388441089676667 51972925647582661634515001)
    ·
      refine ⟨38979694235686996225886251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51972925647582661634515001 38979694235686996225886251)
      ·
        refine ⟨58469541353530494338829377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38979694235686996225886251 58469541353530494338829377)
        ·
          refine ⟨43852156015147870754122033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58469541353530494338829377 43852156015147870754122033)
          ·
            refine ⟨32889117011360903065591525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43852156015147870754122033 32889117011360903065591525)
            ·
              refine ⟨6166709439630169324798411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32889117011360903065591525 6166709439630169324798411)
              ·
                refine ⟨9250064159445253987197617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166709439630169324798411 9250064159445253987197617)
                ·
                  refine ⟨6937548119583940490398213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9250064159445253987197617 6937548119583940490398213)
                  ·
                    refine ⟨1300790272421988841949665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6937548119583940490398213 1300790272421988841949665)
                    ·
                      refine ⟨975592704316491631462249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300790272421988841949665 975592704316491631462249)
                      ·
                        rfl

theorem cell23_1899960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_1899960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899960 prefixEnd_1899960 := by exact prefixLift 1899960
  have htrace : WordTrace (prefixWord ++ tailWord_1899960) baseStart_1899960 baseEnd_1899960 := by
    simpa [prefixWord, tailWord_1899960, baseEnd_1899960] using wordTrace_append hprefix tailTrace_1899960
  have hstable : (prefixWord ++ tailWord_1899960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899960).length < 2 ^ (prefixWord ++ tailWord_1899960).sum := by decide
  have hdescent : baseEnd_1899960 < baseStart_1899960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899980 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1899980 : Nat := 118140960795 + 1899980 * 2 ^ 59
def prefixEnd_1899980 : Nat := 4983230072969 + 3 ^ 40 * 1899980 * 2
def baseEnd_1899980 : Nat := 975602973929581553212157

theorem tailTrace_1899980 : CollatzResearch.WordTrace tailWord_1899980 prefixEnd_1899980 975602973929581553212157 := by
  unfold tailWord_1899980
  simp only [CollatzResearch.WordTrace]
  refine ⟨34648981828352212797540697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46198642437802950396720929 34648981828352212797540697)
  ·
    refine ⟨25986736371264159598155523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34648981828352212797540697 25986736371264159598155523)
    ·
      refine ⟨38980104556896239397233285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25986736371264159598155523 38980104556896239397233285)
      ·
        refine ⟨7308769604418044886981241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38980104556896239397233285 7308769604418044886981241)
        ·
          refine ⟨5481577203313533665235931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7308769604418044886981241 5481577203313533665235931)
          ·
            refine ⟨8222365804970300497853897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481577203313533665235931 8222365804970300497853897)
            ·
              refine ⟨6166774353727725373390423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8222365804970300497853897 6166774353727725373390423)
              ·
                refine ⟨9250161530591588060085635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6166774353727725373390423 9250161530591588060085635)
                ·
                  refine ⟨13875242295887382090128453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9250161530591588060085635 13875242295887382090128453)
                  ·
                    refine ⟨2601607930478884141899085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13875242295887382090128453 2601607930478884141899085)
                    ·
                      refine ⟨975602973929581553212157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601607930478884141899085 975602973929581553212157)
                      ·
                        rfl

theorem cell23_1899980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1899980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899980 prefixEnd_1899980 := by exact prefixLift 1899980
  have htrace : WordTrace (prefixWord ++ tailWord_1899980) baseStart_1899980 baseEnd_1899980 := by
    simpa [prefixWord, tailWord_1899980, baseEnd_1899980] using wordTrace_append hprefix tailTrace_1899980
  have hstable : (prefixWord ++ tailWord_1899980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899980).length < 2 ^ (prefixWord ++ tailWord_1899980).sum := by decide
  have hdescent : baseEnd_1899980 < baseStart_1899980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899997 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1899997 : Nat := 118140960795 + 1899997 * 2 ^ 59
def prefixEnd_1899997 : Nat := 4983230072969 + 3 ^ 40 * 1899997 * 2
def baseEnd_1899997 : Nat := 975611703100707986699579

theorem tailTrace_1899997 : CollatzResearch.WordTrace tailWord_1899997 prefixEnd_1899997 975611703100707986699579 := by
  unfold tailWord_1899997
  simp only [CollatzResearch.WordTrace]
  refine ⟨69298583697642837498450245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199055798428558332300163 69298583697642837498450245)
  ·
    refine ⟨12993484443308032030959421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69298583697642837498450245 12993484443308032030959421)
    ·
      refine ⟨4872556666240512011609783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12993484443308032030959421 4872556666240512011609783)
      ·
        refine ⟨7308834999360768017414675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872556666240512011609783 7308834999360768017414675)
        ·
          refine ⟨10963252499041152026122013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308834999360768017414675 10963252499041152026122013)
          ·
            refine ⟨4111219687140432009795755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10963252499041152026122013 4111219687140432009795755)
            ·
              refine ⟨6166829530710648014693633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111219687140432009795755 6166829530710648014693633)
              ·
                refine ⟨4625122148032986011020225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6166829530710648014693633 4625122148032986011020225)
                ·
                  refine ⟨3468841611024739508265169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625122148032986011020225 3468841611024739508265169)
                  ·
                    refine ⟨2601631208268554631198877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3468841611024739508265169 2601631208268554631198877)
                    ·
                      refine ⟨975611703100707986699579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2601631208268554631198877 975611703100707986699579)
                      ·
                        rfl

theorem cell23_1899997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1899997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1899997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1899997 prefixEnd_1899997 := by exact prefixLift 1899997
  have htrace : WordTrace (prefixWord ++ tailWord_1899997) baseStart_1899997 baseEnd_1899997 := by
    simpa [prefixWord, tailWord_1899997, baseEnd_1899997] using wordTrace_append hprefix tailTrace_1899997
  have hstable : (prefixWord ++ tailWord_1899997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899997).length < 2 ^ (prefixWord ++ tailWord_1899997).sum := by decide
  have hdescent : baseEnd_1899997 < baseStart_1899997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900017 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 6]
def baseStart_1900017 : Nat := 118140960795 + 1900017 * 2 ^ 59
def prefixEnd_1900017 : Nat := 4983230072969 + 3 ^ 40 * 1900017 * 2
def baseEnd_1900017 : Nat := 108402441412644212049943

theorem tailTrace_1900017 : CollatzResearch.WordTrace tailWord_1900017 prefixEnd_1900017 108402441412644212049943 := by
  unfold tailWord_1900017
  simp only [CollatzResearch.WordTrace]
  refine ⟨69299313157570380914178305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199542105046920609452203 69299313157570380914178305)
  ·
    refine ⟨51974484868177785685633729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69299313157570380914178305 51974484868177785685633729)
    ·
      refine ⟨38980863651133339264225297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51974484868177785685633729 38980863651133339264225297)
      ·
        refine ⟨29235647738350004448168973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38980863651133339264225297 29235647738350004448168973)
        ·
          refine ⟨10963367901881251668063365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29235647738350004448168973 10963367901881251668063365)
          ·
            refine ⟨2055631481602734687761881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10963367901881251668063365 2055631481602734687761881)
            ·
              refine ⟨1541723611202051015821411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055631481602734687761881 1541723611202051015821411)
              ·
                refine ⟨2312585416803076523732117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541723611202051015821411 2312585416803076523732117)
                ·
                  refine ⟨108402441412644212049943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2312585416803076523732117 108402441412644212049943)
                  ·
                    rfl

theorem cell23_1900017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 6].length) (baseStart_1900017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900017 prefixEnd_1900017 := by exact prefixLift 1900017
  have htrace : WordTrace (prefixWord ++ tailWord_1900017) baseStart_1900017 baseEnd_1900017 := by
    simpa [prefixWord, tailWord_1900017, baseEnd_1900017] using wordTrace_append hprefix tailTrace_1900017
  have hstable : (prefixWord ++ tailWord_1900017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900017).length < 2 ^ (prefixWord ++ tailWord_1900017).sum := by decide
  have hdescent : baseEnd_1900017 < baseStart_1900017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900063 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1900063 : Nat := 118140960795 + 1900063 * 2 ^ 59
def prefixEnd_1900063 : Nat := 4983230072969 + 3 ^ 40 * 1900063 * 2
def baseEnd_1900063 : Nat := 975645592823904728474275

theorem tailTrace_1900063 : CollatzResearch.WordTrace tailWord_1900063 prefixEnd_1900063 975645592823904728474275 := by
  unfold tailWord_1900063
  simp only [CollatzResearch.WordTrace]
  refine ⟨69300990915403730770352843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46200660610269153846901895 69300990915403730770352843)
  ·
    refine ⟨103951486373105596155529265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69300990915403730770352843 103951486373105596155529265)
    ·
      refine ⟨77963614779829197116646949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103951486373105596155529265 77963614779829197116646949)
      ·
        refine ⟨14618177771217974459371303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77963614779829197116646949 14618177771217974459371303)
        ·
          refine ⟨21927266656826961689056955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14618177771217974459371303 21927266656826961689056955)
          ·
            refine ⟨32890899985240442533585433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21927266656826961689056955 32890899985240442533585433)
            ·
              refine ⟨24668174988930331900189075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32890899985240442533585433 24668174988930331900189075)
              ·
                refine ⟨37002262483395497850283613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24668174988930331900189075 37002262483395497850283613)
                ·
                  refine ⟨13875848431273311693856355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37002262483395497850283613 13875848431273311693856355)
                  ·
                    refine ⟨20813772646909967540784533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13875848431273311693856355 20813772646909967540784533)
                    ·
                      refine ⟨975645592823904728474275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20813772646909967540784533 975645592823904728474275)
                      ·
                        rfl

theorem cell23_1900063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1900063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900063 prefixEnd_1900063 := by exact prefixLift 1900063
  have htrace : WordTrace (prefixWord ++ tailWord_1900063) baseStart_1900063 baseEnd_1900063 := by
    simpa [prefixWord, tailWord_1900063, baseEnd_1900063] using wordTrace_append hprefix tailTrace_1900063
  have hstable : (prefixWord ++ tailWord_1900063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900063).length < 2 ^ (prefixWord ++ tailWord_1900063).sum := by decide
  have hdescent : baseEnd_1900063 < baseStart_1900063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900090 : List Nat := [3, 1, 1, 1, 3, 2, 5, 7]
def baseStart_1900090 : Nat := 118140960795 + 1900090 * 2 ^ 59
def prefixEnd_1900090 : Nat := 4983230072969 + 3 ^ 40 * 1900090 * 2
def baseEnd_1900090 : Nat := 36135535437095411956913

theorem tailTrace_1900090 : CollatzResearch.WordTrace tailWord_1900090 prefixEnd_1900090 36135535437095411956913 := by
  unfold tailWord_1900090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325493921576478595396431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46201317124203942921057149 17325493921576478595396431)
  ·
    refine ⟨25988240882364717893094647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17325493921576478595396431 25988240882364717893094647)
    ·
      refine ⟨38982361323547076839641971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988240882364717893094647 38982361323547076839641971)
      ·
        refine ⟨58473541985320615259462957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38982361323547076839641971 58473541985320615259462957)
        ·
          refine ⟨21927578244495230722298609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58473541985320615259462957 21927578244495230722298609)
          ·
            refine ⟨16445683683371423041723957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21927578244495230722298609 16445683683371423041723957)
            ·
              refine ⟨1541782845316070910161621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16445683683371423041723957 1541782845316070910161621)
              ·
                refine ⟨36135535437095411956913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1541782845316070910161621 36135535437095411956913)
                ·
                  rfl

theorem cell23_1900090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_1900090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900090 prefixEnd_1900090 := by exact prefixLift 1900090
  have htrace : WordTrace (prefixWord ++ tailWord_1900090) baseStart_1900090 baseEnd_1900090 := by
    simpa [prefixWord, tailWord_1900090, baseEnd_1900090] using wordTrace_append hprefix tailTrace_1900090
  have hstable : (prefixWord ++ tailWord_1900090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900090).length < 2 ^ (prefixWord ++ tailWord_1900090).sum := by decide
  have hdescent : baseEnd_1900090 < baseStart_1900090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900101 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 1, 2, 2]
def baseStart_1900101 : Nat := 118140960795 + 1900101 * 2 ^ 59
def prefixEnd_1900101 : Nat := 4983230072969 + 3 ^ 40 * 1900101 * 2
def baseEnd_1900101 : Nat := 975665105088775579799101

theorem tailTrace_1900101 : CollatzResearch.WordTrace tailWord_1900101 prefixEnd_1900101 975665105088775579799101 := by
  unfold tailWord_1900101
  simp only [CollatzResearch.WordTrace]
  refine ⟨69302376889266063260236157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46201584592844042173490771 69302376889266063260236157)
  ·
    refine ⟨25988391333474773722588559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69302376889266063260236157 25988391333474773722588559)
    ·
      refine ⟨38982587000212160583882839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25988391333474773722588559 38982587000212160583882839)
      ·
        refine ⟨58473880500318240875824259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38982587000212160583882839 58473880500318240875824259)
        ·
          refine ⟨87710820750477361313736389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58473880500318240875824259 87710820750477361313736389)
          ·
            refine ⟨16445778890714505246325573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87710820750477361313736389 16445778890714505246325573)
            ·
              refine ⟨3083583542008969733686045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16445778890714505246325573 3083583542008969733686045)
              ·
                refine ⟨1156343828253363650132267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3083583542008969733686045 1156343828253363650132267)
                ·
                  refine ⟨1734515742380045475198401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156343828253363650132267 1734515742380045475198401)
                  ·
                    refine ⟨1300886806785034106398801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1734515742380045475198401 1300886806785034106398801)
                    ·
                      refine ⟨975665105088775579799101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300886806785034106398801 975665105088775579799101)
                      ·
                        rfl

theorem cell23_1900101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_1900101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900101 prefixEnd_1900101 := by exact prefixLift 1900101
  have htrace : WordTrace (prefixWord ++ tailWord_1900101) baseStart_1900101 baseEnd_1900101 := by
    simpa [prefixWord, tailWord_1900101, baseEnd_1900101] using wordTrace_append hprefix tailTrace_1900101
  have hstable : (prefixWord ++ tailWord_1900101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900101).length < 2 ^ (prefixWord ++ tailWord_1900101).sum := by decide
  have hdescent : baseEnd_1900101 < baseStart_1900101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900144 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2]
def baseStart_1900144 : Nat := 118140960795 + 1900144 * 2 ^ 59
def prefixEnd_1900144 : Nat := 4983230072969 + 3 ^ 40 * 1900144 * 2
def baseEnd_1900144 : Nat := 975687184756918911561403

theorem tailTrace_1900144 : CollatzResearch.WordTrace tailWord_1900144 prefixEnd_1900144 975687184756918911561403 := by
  unfold tailWord_1900144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34651972614055140802025743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46202630152073521069367657 34651972614055140802025743)
  ·
    refine ⟨51977958921082711203038615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34651972614055140802025743 51977958921082711203038615)
    ·
      refine ⟨77966938381624066804557923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51977958921082711203038615 77966938381624066804557923)
      ·
        refine ⟨116950407572436100206836885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77966938381624066804557923 116950407572436100206836885)
        ·
          refine ⟨5482050354957942197195479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116950407572436100206836885 5482050354957942197195479)
          ·
            refine ⟨8223075532436913295793219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482050354957942197195479 8223075532436913295793219)
            ·
              refine ⟨12334613298655369943689829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8223075532436913295793219 12334613298655369943689829)
              ·
                refine ⟨2312739993497881864441843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12334613298655369943689829 2312739993497881864441843)
                ·
                  refine ⟨3469109990246822796662765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312739993497881864441843 3469109990246822796662765)
                  ·
                    refine ⟨1300916246342558548748537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469109990246822796662765 1300916246342558548748537)
                    ·
                      refine ⟨975687184756918911561403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1300916246342558548748537 975687184756918911561403)
                      ·
                        rfl

theorem cell23_1900144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2].length) (baseStart_1900144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900144 prefixEnd_1900144 := by exact prefixLift 1900144
  have htrace : WordTrace (prefixWord ++ tailWord_1900144) baseStart_1900144 baseEnd_1900144 := by
    simpa [prefixWord, tailWord_1900144, baseEnd_1900144] using wordTrace_append hprefix tailTrace_1900144
  have hstable : (prefixWord ++ tailWord_1900144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900144).length < 2 ^ (prefixWord ++ tailWord_1900144).sum := by decide
  have hdescent : baseEnd_1900144 < baseStart_1900144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900160 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1900160 : Nat := 118140960795 + 1900160 * 2 ^ 59
def prefixEnd_1900160 : Nat := 4983230072969 + 3 ^ 40 * 1900160 * 2
def baseEnd_1900160 : Nat := 975695400447390848961329

theorem tailTrace_1900160 : CollatzResearch.WordTrace tailWord_1900160 prefixEnd_1900160 975695400447390848961329 := by
  unfold tailWord_1900160
  simp only [CollatzResearch.WordTrace]
  refine ⟨34652264398026158168316967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46203019197368210891089289 34652264398026158168316967)
  ·
    refine ⟨51978396597039237252475451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34652264398026158168316967 51978396597039237252475451)
    ·
      refine ⟨77967594895558855878713177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51978396597039237252475451 77967594895558855878713177)
      ·
        refine ⟨58475696171669141909034883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77967594895558855878713177 58475696171669141909034883)
        ·
          refine ⟨87713544257503712863552325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58475696171669141909034883 87713544257503712863552325)
          ·
            refine ⟨16446289548281946161916061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87713544257503712863552325 16446289548281946161916061)
            ·
              refine ⟨6167358580605729810718523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16446289548281946161916061 6167358580605729810718523)
              ·
                refine ⟨9251037870908594716077785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167358580605729810718523 9251037870908594716077785)
                ·
                  refine ⟨6938278403181446037058339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9251037870908594716077785 6938278403181446037058339)
                  ·
                    refine ⟨10407417604772169055587509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938278403181446037058339 10407417604772169055587509)
                    ·
                      refine ⟨975695400447390848961329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10407417604772169055587509 975695400447390848961329)
                      ·
                        rfl

theorem cell23_1900160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1900160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900160 prefixEnd_1900160 := by exact prefixLift 1900160
  have htrace : WordTrace (prefixWord ++ tailWord_1900160) baseStart_1900160 baseEnd_1900160 := by
    simpa [prefixWord, tailWord_1900160, baseEnd_1900160] using wordTrace_append hprefix tailTrace_1900160
  have hstable : (prefixWord ++ tailWord_1900160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900160).length < 2 ^ (prefixWord ++ tailWord_1900160).sum := by decide
  have hdescent : baseEnd_1900160 < baseStart_1900160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900210 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1900210 : Nat := 118140960795 + 1900210 * 2 ^ 59
def prefixEnd_1900210 : Nat := 4983230072969 + 3 ^ 40 * 1900210 * 2
def baseEnd_1900210 : Nat := 325240358160038551112033

theorem tailTrace_1900210 : CollatzResearch.WordTrace tailWord_1900210 prefixEnd_1900210 325240358160038551112033 := by
  unfold tailWord_1900210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326588111467793718988521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46204234963914116583969389 17326588111467793718988521)
  ·
    refine ⟨12994941083600845289241391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17326588111467793718988521 12994941083600845289241391)
    ·
      refine ⟨19492411625401267933862087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12994941083600845289241391 19492411625401267933862087)
      ·
        refine ⟨29238617438101901900793131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19492411625401267933862087 29238617438101901900793131)
        ·
          refine ⟨43857926157152852851189697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29238617438101901900793131 43857926157152852851189697)
          ·
            refine ⟨32893444617864639638392273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43857926157152852851189697 32893444617864639638392273)
            ·
              refine ⟨24670083463398479728794205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32893444617864639638392273 24670083463398479728794205)
              ·
                refine ⟨9251281298774429898297827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24670083463398479728794205 9251281298774429898297827)
                ·
                  refine ⟨13876921948161644847446741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9251281298774429898297827 13876921948161644847446741)
                  ·
                    refine ⟨325240358160038551112033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13876921948161644847446741 325240358160038551112033)
                    ·
                      rfl

theorem cell23_1900210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1900210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900210 prefixEnd_1900210 := by exact prefixLift 1900210
  have htrace : WordTrace (prefixWord ++ tailWord_1900210) baseStart_1900210 baseEnd_1900210 := by
    simpa [prefixWord, tailWord_1900210, baseEnd_1900210] using wordTrace_append hprefix tailTrace_1900210
  have hstable : (prefixWord ++ tailWord_1900210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900210).length < 2 ^ (prefixWord ++ tailWord_1900210).sum := by decide
  have hdescent : baseEnd_1900210 < baseStart_1900210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900264 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1900264 : Nat := 118140960795 + 1900264 * 2 ^ 59
def prefixEnd_1900264 : Nat := 4983230072969 + 3 ^ 40 * 1900264 * 2
def baseEnd_1900264 : Nat := 975748802435458442060851

theorem tailTrace_1900264 : CollatzResearch.WordTrace tailWord_1900264 prefixEnd_1900264 975748802435458442060851 := by
  unfold tailWord_1900264
  simp only [CollatzResearch.WordTrace]
  refine ⟨34654160993837771049209923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46205547991783694732279897 34654160993837771049209923)
  ·
    refine ⟨51981241490756656573814885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34654160993837771049209923 51981241490756656573814885)
    ·
      refine ⟨9746482779516873107590291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51981241490756656573814885 9746482779516873107590291)
      ·
        refine ⟨14619724169275309661385437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9746482779516873107590291 14619724169275309661385437)
        ·
          refine ⟨5482396563478241123019539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14619724169275309661385437 5482396563478241123019539)
          ·
            refine ⟨8223594845217361684529309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482396563478241123019539 8223594845217361684529309)
            ·
              refine ⟨3083848066956510631698491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8223594845217361684529309 3083848066956510631698491)
              ·
                refine ⟨4625772100434765947547737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083848066956510631698491 4625772100434765947547737)
                ·
                  refine ⟨3469329075326074460660803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625772100434765947547737 3469329075326074460660803)
                  ·
                    refine ⟨5203993612989111690991205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3469329075326074460660803 5203993612989111690991205)
                    ·
                      refine ⟨975748802435458442060851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5203993612989111690991205 975748802435458442060851)
                      ·
                        rfl

theorem cell23_1900264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1900264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900264 prefixEnd_1900264 := by exact prefixLift 1900264
  have htrace : WordTrace (prefixWord ++ tailWord_1900264) baseStart_1900264 baseEnd_1900264 := by
    simpa [prefixWord, tailWord_1900264, baseEnd_1900264] using wordTrace_append hprefix tailTrace_1900264
  have hstable : (prefixWord ++ tailWord_1900264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900264).length < 2 ^ (prefixWord ++ tailWord_1900264).sum := by decide
  have hdescent : baseEnd_1900264 < baseStart_1900264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900287 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 6]
def baseStart_1900287 : Nat := 118140960795 + 1900287 * 2 ^ 59
def prefixEnd_1900287 : Nat := 4983230072969 + 3 ^ 40 * 1900287 * 2
def baseEnd_1900287 : Nat := 108417845832279094674805

theorem tailTrace_1900287 : CollatzResearch.WordTrace tailWord_1900287 prefixEnd_1900287 108417845832279094674805 := by
  unfold tailWord_1900287
  simp only [CollatzResearch.WordTrace]
  refine ⟨69309160866592217026507115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46206107244394811351004743 69309160866592217026507115)
  ·
    refine ⟨103963741299888325539760673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69309160866592217026507115 103963741299888325539760673)
    ·
      refine ⟨77972805974916244154820505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103963741299888325539760673 77972805974916244154820505)
      ·
        refine ⟨58479604481187183116115379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77972805974916244154820505 58479604481187183116115379)
        ·
          refine ⟨87719406721780774674173069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58479604481187183116115379 87719406721780774674173069)
          ·
            refine ⟨32894777520667790502814901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87719406721780774674173069 32894777520667790502814901)
            ·
              refine ⟨3083885392562605359638897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32894777520667790502814901 3083885392562605359638897)
              ·
                refine ⟨2312914044421954019729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083885392562605359638897 2312914044421954019729173)
                ·
                  refine ⟨108417845832279094674805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2312914044421954019729173 108417845832279094674805)
                  ·
                    rfl

theorem cell23_1900287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 6].length) (baseStart_1900287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900287 prefixEnd_1900287 := by exact prefixLift 1900287
  have htrace : WordTrace (prefixWord ++ tailWord_1900287) baseStart_1900287 baseEnd_1900287 := by
    simpa [prefixWord, tailWord_1900287, baseEnd_1900287] using wordTrace_append hprefix tailTrace_1900287
  have hstable : (prefixWord ++ tailWord_1900287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900287).length < 2 ^ (prefixWord ++ tailWord_1900287).sum := by decide
  have hdescent : baseEnd_1900287 < baseStart_1900287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900357 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_1900357 : Nat := 118140960795 + 1900357 * 2 ^ 59
def prefixEnd_1900357 : Nat := 4983230072969 + 3 ^ 40 * 1900357 * 2
def baseEnd_1900357 : Nat := 975796556136326578197923

theorem tailTrace_1900357 : CollatzResearch.WordTrace tailWord_1900357 prefixEnd_1900357 975796556136326578197923 := by
  unfold tailWord_1900357
  simp only [CollatzResearch.WordTrace]
  refine ⟨69311713976338618981555325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46207809317559079321036883 69311713976338618981555325)
  ·
    refine ⟨25991892741126982118083247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69311713976338618981555325 25991892741126982118083247)
    ·
      refine ⟨38987839111690473177124871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25991892741126982118083247 38987839111690473177124871)
      ·
        refine ⟨58481758667535709765687307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38987839111690473177124871 58481758667535709765687307)
        ·
          refine ⟨87722638001303564648530961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58481758667535709765687307 87722638001303564648530961)
          ·
            refine ⟨65791978500977673486398221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87722638001303564648530961 65791978500977673486398221)
            ·
              refine ⟨24671991937866627557399333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65791978500977673486398221 24671991937866627557399333)
              ·
                refine ⟨4625998488349992667012375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24671991937866627557399333 4625998488349992667012375)
                ·
                  refine ⟨6938997732524989000518563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625998488349992667012375 6938997732524989000518563)
                  ·
                    refine ⟨10408496598787483500777845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938997732524989000518563 10408496598787483500777845)
                    ·
                      refine ⟨975796556136326578197923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10408496598787483500777845 975796556136326578197923)
                      ·
                        rfl

theorem cell23_1900357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_1900357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900357 prefixEnd_1900357 := by exact prefixLift 1900357
  have htrace : WordTrace (prefixWord ++ tailWord_1900357) baseStart_1900357 baseEnd_1900357 := by
    simpa [prefixWord, tailWord_1900357, baseEnd_1900357] using wordTrace_append hprefix tailTrace_1900357
  have hstable : (prefixWord ++ tailWord_1900357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900357).length < 2 ^ (prefixWord ++ tailWord_1900357).sum := by decide
  have hdescent : baseEnd_1900357 < baseStart_1900357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900384 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1900384 : Nat := 118140960795 + 1900384 * 2 ^ 59
def prefixEnd_1900384 : Nat := 4983230072969 + 3 ^ 40 * 1900384 * 2
def baseEnd_1900384 : Nat := 975810420113997972560299

theorem tailTrace_1900384 : CollatzResearch.WordTrace tailWord_1900384 prefixEnd_1900384 975810420113997972560299 := by
  unfold tailWord_1900384
  simp only [CollatzResearch.WordTrace]
  refine ⟨34656349373620401296394103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46208465831493868395192137 34656349373620401296394103)
  ·
    refine ⟨51984524060430601944591155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34656349373620401296394103 51984524060430601944591155)
    ·
      refine ⟨77976786090645902916886733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51984524060430601944591155 77976786090645902916886733)
      ·
        refine ⟨29241294783992213593832525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77976786090645902916886733 29241294783992213593832525)
        ·
          refine ⟨10965485543997080097687197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29241294783992213593832525 10965485543997080097687197)
          ·
            refine ⟨4112057078998905036632699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10965485543997080097687197 4112057078998905036632699)
            ·
              refine ⟨6168085618498357554949049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4112057078998905036632699 6168085618498357554949049)
              ·
                refine ⟨4626064213873768166211787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168085618498357554949049 4626064213873768166211787)
                ·
                  refine ⟨6939096320810652249317681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626064213873768166211787 6939096320810652249317681)
                  ·
                    refine ⟨5204322240607989186988261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6939096320810652249317681 5204322240607989186988261)
                    ·
                      refine ⟨975810420113997972560299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5204322240607989186988261 975810420113997972560299)
                      ·
                        rfl

theorem cell23_1900384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1900384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900384 prefixEnd_1900384 := by exact prefixLift 1900384
  have htrace : WordTrace (prefixWord ++ tailWord_1900384) baseStart_1900384 baseEnd_1900384 := by
    simpa [prefixWord, tailWord_1900384, baseEnd_1900384] using wordTrace_append hprefix tailTrace_1900384
  have hstable : (prefixWord ++ tailWord_1900384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900384).length < 2 ^ (prefixWord ++ tailWord_1900384).sum := by decide
  have hdescent : baseEnd_1900384 < baseStart_1900384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900388 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_1900388 : Nat := 118140960795 + 1900388 * 2 ^ 59
def prefixEnd_1900388 : Nat := 4983230072969 + 3 ^ 40 * 1900388 * 2
def baseEnd_1900388 : Nat := 975812474036615956910281

theorem tailTrace_1900388 : CollatzResearch.WordTrace tailWord_1900388 prefixEnd_1900388 975812474036615956910281 := by
  unfold tailWord_1900388
  simp only [CollatzResearch.WordTrace]
  refine ⟨34656422319613155637966909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46208563092817540850622545 34656422319613155637966909)
  ·
    refine ⟨12996158369854933364237591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34656422319613155637966909 12996158369854933364237591)
    ·
      refine ⟨19494237554782400046356387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12996158369854933364237591 19494237554782400046356387)
      ·
        refine ⟨29241356332173600069534581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19494237554782400046356387 29241356332173600069534581)
        ·
          refine ⟨2741377156141275006518867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29241356332173600069534581 2741377156141275006518867)
          ·
            refine ⟨4112065734211912509778301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741377156141275006518867 4112065734211912509778301)
            ·
              refine ⟨1542024650329467191166863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4112065734211912509778301 1542024650329467191166863)
              ·
                refine ⟨2313036975494200786750295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542024650329467191166863 2313036975494200786750295)
                ·
                  refine ⟨3469555463241301180125443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313036975494200786750295 3469555463241301180125443)
                  ·
                    refine ⟨5204333194861951770188165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3469555463241301180125443 5204333194861951770188165)
                    ·
                      refine ⟨975812474036615956910281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5204333194861951770188165 975812474036615956910281)
                      ·
                        rfl

theorem cell23_1900388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_1900388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900388 prefixEnd_1900388 := by exact prefixLift 1900388
  have htrace : WordTrace (prefixWord ++ tailWord_1900388) baseStart_1900388 baseEnd_1900388 := by
    simpa [prefixWord, tailWord_1900388, baseEnd_1900388] using wordTrace_append hprefix tailTrace_1900388
  have hstable : (prefixWord ++ tailWord_1900388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900388).length < 2 ^ (prefixWord ++ tailWord_1900388).sum := by decide
  have hdescent : baseEnd_1900388 < baseStart_1900388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900394 : List Nat := [3, 1, 3, 4, 1, 11]
def baseStart_1900394 : Nat := 118140960795 + 1900394 * 2 ^ 59
def prefixEnd_1900394 : Nat := 4983230072969 + 3 ^ 40 * 1900394 * 2
def baseEnd_1900394 : Nat := 4015701872100999726071

theorem tailTrace_1900394 : CollatzResearch.WordTrace tailWord_1900394 prefixEnd_1900394 4015701872100999726071 := by
  unfold tailWord_1900394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17328265869301143575163059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46208708984803049533768157 17328265869301143575163059)
  ·
    refine ⟨25992398803951715362744589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17328265869301143575163059 25992398803951715362744589)
    ·
      refine ⟨9747149551481893261029221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25992398803951715362744589 9747149551481893261029221)
      ·
        refine ⟨1827590540902854986442979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9747149551481893261029221 1827590540902854986442979)
        ·
          refine ⟨2741385811354282479664469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827590540902854986442979 2741385811354282479664469)
          ·
            refine ⟨4015701872100999726071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2741385811354282479664469 4015701872100999726071)
            ·
              rfl

theorem cell23_1900394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 11].length) (baseStart_1900394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900394 prefixEnd_1900394 := by exact prefixLift 1900394
  have htrace : WordTrace (prefixWord ++ tailWord_1900394) baseStart_1900394 baseEnd_1900394 := by
    simpa [prefixWord, tailWord_1900394, baseEnd_1900394] using wordTrace_append hprefix tailTrace_1900394
  have hstable : (prefixWord ++ tailWord_1900394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900394).length < 2 ^ (prefixWord ++ tailWord_1900394).sum := by decide
  have hdescent : baseEnd_1900394 < baseStart_1900394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900398 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1900398 : Nat := 118140960795 + 1900398 * 2 ^ 59
def prefixEnd_1900398 : Nat := 4983230072969 + 3 ^ 40 * 1900398 * 2
def baseEnd_1900398 : Nat := 325272536281053639261745

theorem tailTrace_1900398 : CollatzResearch.WordTrace tailWord_1900398 prefixEnd_1900398 325272536281053639261745 := by
  unfold tailWord_1900398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664151171148760372974731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46208806246126721989198565 8664151171148760372974731)
  ·
    refine ⟨12996226756723140559462097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8664151171148760372974731 12996226756723140559462097)
    ·
      refine ⟨9747170067542355419596573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12996226756723140559462097 9747170067542355419596573)
      ·
        refine ⟨3655188775328383282348715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9747170067542355419596573 3655188775328383282348715)
        ·
          refine ⟨5482783162992574923523073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655188775328383282348715 5482783162992574923523073)
          ·
            refine ⟨4112087372244431192642305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5482783162992574923523073 4112087372244431192642305)
            ·
              refine ⟨3084065529183323394481729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112087372244431192642305 3084065529183323394481729)
              ·
                refine ⟨2313049146887492545861297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084065529183323394481729 2313049146887492545861297)
                ·
                  refine ⟨1734786860165619409395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313049146887492545861297 1734786860165619409395973)
                  ·
                    refine ⟨325272536281053639261745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1734786860165619409395973 325272536281053639261745)
                    ·
                      rfl

theorem cell23_1900398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1900398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900398 prefixEnd_1900398 := by exact prefixLift 1900398
  have htrace : WordTrace (prefixWord ++ tailWord_1900398) baseStart_1900398 baseEnd_1900398 := by
    simpa [prefixWord, tailWord_1900398, baseEnd_1900398] using wordTrace_append hprefix tailTrace_1900398
  have hstable : (prefixWord ++ tailWord_1900398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900398).length < 2 ^ (prefixWord ++ tailWord_1900398).sum := by decide
  have hdescent : baseEnd_1900398 < baseStart_1900398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900405 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1900405 : Nat := 118140960795 + 1900405 * 2 ^ 59
def prefixEnd_1900405 : Nat := 4983230072969 + 3 ^ 40 * 1900405 * 2
def baseEnd_1900405 : Nat := 975821203207742390397703

theorem tailTrace_1900405 : CollatzResearch.WordTrace tailWord_1900405 prefixEnd_1900405 975821203207742390397703 := by
  unfold tailWord_1900405
  simp only [CollatzResearch.WordTrace]
  refine ⟨69313464680164723179302669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46208976453443148786201779 69313464680164723179302669)
  ·
    refine ⟨25992549255061771192238501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69313464680164723179302669 25992549255061771192238501)
    ·
      refine ⟨4873602985324082098544719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25992549255061771192238501 4873602985324082098544719)
      ·
        refine ⟨7310404477986123147817079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873602985324082098544719 7310404477986123147817079)
        ·
          refine ⟨10965606716979184721725619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310404477986123147817079 10965606716979184721725619)
          ·
            refine ⟨16448410075468777082588429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10965606716979184721725619 16448410075468777082588429)
            ·
              refine ⟨6168153778300791405970661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16448410075468777082588429 6168153778300791405970661)
              ·
                refine ⟨1156528833431398388619499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6168153778300791405970661 1156528833431398388619499)
                ·
                  refine ⟨1734793250147097582929249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156528833431398388619499 1734793250147097582929249)
                  ·
                    refine ⟨1301094937610323187196937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1734793250147097582929249 1301094937610323187196937)
                    ·
                      refine ⟨975821203207742390397703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301094937610323187196937 975821203207742390397703)
                      ·
                        rfl

theorem cell23_1900405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1900405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900405 prefixEnd_1900405 := by exact prefixLift 1900405
  have htrace : WordTrace (prefixWord ++ tailWord_1900405) baseStart_1900405 baseEnd_1900405 := by
    simpa [prefixWord, tailWord_1900405, baseEnd_1900405] using wordTrace_append hprefix tailTrace_1900405
  have hstable : (prefixWord ++ tailWord_1900405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900405).length < 2 ^ (prefixWord ++ tailWord_1900405).sum := by decide
  have hdescent : baseEnd_1900405 < baseStart_1900405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900421 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 3]
def baseStart_1900421 : Nat := 118140960795 + 1900421 * 2 ^ 59
def prefixEnd_1900421 : Nat := 4983230072969 + 3 ^ 40 * 1900421 * 2
def baseEnd_1900421 : Nat := 975829418898214327797629

theorem tailTrace_1900421 : CollatzResearch.WordTrace tailWord_1900421 prefixEnd_1900421 975829418898214327797629 := by
  unfold tailWord_1900421
  simp only [CollatzResearch.WordTrace]
  refine ⟨69314048248106757911885117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46209365498737838607923411 69314048248106757911885117)
  ·
    refine ⟨25992768093040034216956919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69314048248106757911885117 25992768093040034216956919)
    ·
      refine ⟨38989152139560051325435379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25992768093040034216956919 38989152139560051325435379)
      ·
        refine ⟨58483728209340076988153069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38989152139560051325435379 58483728209340076988153069)
        ·
          refine ⟨21931398078502528870557401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58483728209340076988153069 21931398078502528870557401)
          ·
            refine ⟨16448548558876896652918051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21931398078502528870557401 16448548558876896652918051)
            ·
              refine ⟨24672822838315344979377077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16448548558876896652918051 24672822838315344979377077)
              ·
                refine ⟨2313077141092063591816601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24672822838315344979377077 2313077141092063591816601)
                ·
                  refine ⟨1734807855819047693862451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313077141092063591816601 1734807855819047693862451)
                  ·
                    refine ⟨2602211783728571540793677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734807855819047693862451 2602211783728571540793677)
                    ·
                      refine ⟨975829418898214327797629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2602211783728571540793677 975829418898214327797629)
                      ·
                        rfl

theorem cell23_1900421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_1900421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900421 prefixEnd_1900421 := by exact prefixLift 1900421
  have htrace : WordTrace (prefixWord ++ tailWord_1900421) baseStart_1900421 baseEnd_1900421 := by
    simpa [prefixWord, tailWord_1900421, baseEnd_1900421] using wordTrace_append hprefix tailTrace_1900421
  have hstable : (prefixWord ++ tailWord_1900421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900421).length < 2 ^ (prefixWord ++ tailWord_1900421).sum := by decide
  have hdescent : baseEnd_1900421 < baseStart_1900421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900427 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4]
def baseStart_1900427 : Nat := 118140960795 + 1900427 * 2 ^ 59
def prefixEnd_1900427 : Nat := 4983230072969 + 3 ^ 40 * 1900427 * 2
def baseEnd_1900427 : Nat := 975832499782141304322601

theorem tailTrace_1900427 : CollatzResearch.WordTrace tailWord_1900427 prefixEnd_1900427 975832499782141304322601 := by
  unfold tailWord_1900427
  simp only [CollatzResearch.WordTrace]
  refine ⟨69314267086085020936603535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46209511390723347291069023 69314267086085020936603535)
  ·
    refine ⟨103971400629127531404905303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69314267086085020936603535 103971400629127531404905303)
    ·
      refine ⟨155957100943691297107357955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103971400629127531404905303 155957100943691297107357955)
      ·
        refine ⟨233935651415536945661036933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155957100943691297107357955 233935651415536945661036933)
        ·
          refine ⟨43862934640413177311444425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233935651415536945661036933 43862934640413177311444425)
          ·
            refine ⟨32897200980309882983583319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43862934640413177311444425 32897200980309882983583319)
            ·
              refine ⟨49345801470464824475374979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32897200980309882983583319 49345801470464824475374979)
              ·
                refine ⟨74018702205697236713062469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49345801470464824475374979 74018702205697236713062469)
                ·
                  refine ⟨13878506663568231883699213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74018702205697236713062469 13878506663568231883699213)
                  ·
                    refine ⟨5204439998838086956387205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13878506663568231883699213 5204439998838086956387205)
                    ·
                      refine ⟨975832499782141304322601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5204439998838086956387205 975832499782141304322601)
                      ·
                        rfl

theorem cell23_1900427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 4].length) (baseStart_1900427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900427 prefixEnd_1900427 := by exact prefixLift 1900427
  have htrace : WordTrace (prefixWord ++ tailWord_1900427) baseStart_1900427 baseEnd_1900427 := by
    simpa [prefixWord, tailWord_1900427, baseEnd_1900427] using wordTrace_append hprefix tailTrace_1900427
  have hstable : (prefixWord ++ tailWord_1900427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900427).length < 2 ^ (prefixWord ++ tailWord_1900427).sum := by decide
  have hdescent : baseEnd_1900427 < baseStart_1900427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900437 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1900437 : Nat := 118140960795 + 1900437 * 2 ^ 59
def prefixEnd_1900437 : Nat := 4983230072969 + 3 ^ 40 * 1900437 * 2
def baseEnd_1900437 : Nat := 325279211529562088399185

theorem tailTrace_1900437 : CollatzResearch.WordTrace tailWord_1900437 prefixEnd_1900437 325279211529562088399185 := by
  unfold tailWord_1900437
  simp only [CollatzResearch.WordTrace]
  refine ⟨69314631816048792644467565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46209754544032528429645043 69314631816048792644467565)
  ·
    refine ⟨25992986931018297241675337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69314631816048792644467565 25992986931018297241675337)
    ·
      refine ⟨19494740198263722931256503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25992986931018297241675337 19494740198263722931256503)
      ·
        refine ⟨29242110297395584396884755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19494740198263722931256503 29242110297395584396884755)
        ·
          refine ⟨43863165446093376595327133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29242110297395584396884755 43863165446093376595327133)
          ·
            refine ⟨16448687042285016223247675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43863165446093376595327133 16448687042285016223247675)
            ·
              refine ⟨24673030563427524334871513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16448687042285016223247675 24673030563427524334871513)
              ·
                refine ⟨18504772922570643251153635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24673030563427524334871513 18504772922570643251153635)
                ·
                  refine ⟨27757159383855964876730453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504772922570643251153635 27757159383855964876730453)
                  ·
                    refine ⟨325279211529562088399185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27757159383855964876730453 325279211529562088399185)
                    ·
                      rfl

theorem cell23_1900437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1900437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900437 prefixEnd_1900437 := by exact prefixLift 1900437
  have htrace : WordTrace (prefixWord ++ tailWord_1900437) baseStart_1900437 baseEnd_1900437 := by
    simpa [prefixWord, tailWord_1900437, baseEnd_1900437] using wordTrace_append hprefix tailTrace_1900437
  have hstable : (prefixWord ++ tailWord_1900437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900437).length < 2 ^ (prefixWord ++ tailWord_1900437).sum := by decide
  have hdescent : baseEnd_1900437 < baseStart_1900437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900455 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1900455 : Nat := 118140960795 + 1900455 * 2 ^ 59
def prefixEnd_1900455 : Nat := 4983230072969 + 3 ^ 40 * 1900455 * 2
def baseEnd_1900455 : Nat := 975846877240467194772473

theorem tailTrace_1900455 : CollatzResearch.WordTrace tailWord_1900455 prefixEnd_1900455 975846877240467194772473 := by
  unfold tailWord_1900455
  simp only [CollatzResearch.WordTrace]
  refine ⟨69315288329983581718622819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46210192219989054479081879 69315288329983581718622819)
  ·
    refine ⟨103972932494975372577934229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69315288329983581718622819 103972932494975372577934229)
    ·
      refine ⟨4873731210701970589590667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103972932494975372577934229 4873731210701970589590667)
      ·
        refine ⟨7310596816052955884386001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873731210701970589590667 7310596816052955884386001)
        ·
          refine ⟨5482947612039716913289501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7310596816052955884386001 5482947612039716913289501)
          ·
            refine ⟨2056105354514893842483563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5482947612039716913289501 2056105354514893842483563)
            ·
              refine ⟨3084158031772340763725345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056105354514893842483563 3084158031772340763725345)
              ·
                refine ⟨2313118523829255572794009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084158031772340763725345 2313118523829255572794009)
                ·
                  refine ⟨1734838892871941679595507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313118523829255572794009 1734838892871941679595507)
                  ·
                    refine ⟨2602258339307912519393261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1734838892871941679595507 2602258339307912519393261)
                    ·
                      refine ⟨975846877240467194772473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2602258339307912519393261 975846877240467194772473)
                      ·
                        rfl

theorem cell23_1900455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1900455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900455 prefixEnd_1900455 := by exact prefixLift 1900455
  have htrace : WordTrace (prefixWord ++ tailWord_1900455) baseStart_1900455 baseEnd_1900455 := by
    simpa [prefixWord, tailWord_1900455, baseEnd_1900455] using wordTrace_append hprefix tailTrace_1900455
  have hstable : (prefixWord ++ tailWord_1900455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900455).length < 2 ^ (prefixWord ++ tailWord_1900455).sum := by decide
  have hdescent : baseEnd_1900455 < baseStart_1900455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900478 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_1900478 : Nat := 118140960795 + 1900478 * 2 ^ 59
def prefixEnd_1900478 : Nat := 4983230072969 + 3 ^ 40 * 1900478 * 2
def baseEnd_1900478 : Nat := 975858687295520604784867

theorem tailTrace_1900478 : CollatzResearch.WordTrace tailWord_1900478 prefixEnd_1900478 975858687295520604784867 := by
  unfold tailWord_1900478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664515901112532080838761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46210751472600171097806725 8664515901112532080838761)
  ·
    refine ⟨6498386925834399060629071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8664515901112532080838761 6498386925834399060629071)
    ·
      refine ⟨9747580388751598590943607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498386925834399060629071 9747580388751598590943607)
      ·
        refine ⟨14621370583127397886415411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9747580388751598590943607 14621370583127397886415411)
        ·
          refine ⟨21932055874691096829623117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14621370583127397886415411 21932055874691096829623117)
          ·
            refine ⟨8224520953009161311108669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21932055874691096829623117 8224520953009161311108669)
            ·
              refine ⟨3084195357378435491665751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8224520953009161311108669 3084195357378435491665751)
              ·
                refine ⟨4626293036067653237498627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084195357378435491665751 4626293036067653237498627)
                ·
                  refine ⟨6939439554101479856247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626293036067653237498627 6939439554101479856247941)
                  ·
                    refine ⟨1301144916394027473046489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939439554101479856247941 1301144916394027473046489)
                    ·
                      refine ⟨975858687295520604784867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301144916394027473046489 975858687295520604784867)
                      ·
                        rfl

theorem cell23_1900478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_1900478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900478 prefixEnd_1900478 := by exact prefixLift 1900478
  have htrace : WordTrace (prefixWord ++ tailWord_1900478) baseStart_1900478 baseEnd_1900478 := by
    simpa [prefixWord, tailWord_1900478, baseEnd_1900478] using wordTrace_append hprefix tailTrace_1900478
  have hstable : (prefixWord ++ tailWord_1900478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900478).length < 2 ^ (prefixWord ++ tailWord_1900478).sum := by decide
  have hdescent : baseEnd_1900478 < baseStart_1900478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900529 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_1900529 : Nat := 118140960795 + 1900529 * 2 ^ 59
def prefixEnd_1900529 : Nat := 4983230072969 + 3 ^ 40 * 1900529 * 2
def baseEnd_1900529 : Nat := 975884874808899905247133

theorem tailTrace_1900529 : CollatzResearch.WordTrace tailWord_1900529 prefixEnd_1900529 975884874808899905247133 := by
  unfold tailWord_1900529
  simp only [CollatzResearch.WordTrace]
  refine ⟨69317987331715492356816641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46211991554476994904544427 69317987331715492356816641)
  ·
    refine ⟨51988490498786619267612481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69317987331715492356816641 51988490498786619267612481)
    ·
      refine ⟨38991367874089964450709361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51988490498786619267612481 38991367874089964450709361)
      ·
        refine ⟨29243525905567473338032021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38991367874089964450709361 29243525905567473338032021)
        ·
          refine ⟨1370790276823475312720251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29243525905567473338032021 1370790276823475312720251)
          ·
            refine ⟨2056185415235212969080377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370790276823475312720251 2056185415235212969080377)
            ·
              refine ⟨1542139061426409726810283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056185415235212969080377 1542139061426409726810283)
              ·
                refine ⟨2313208592139614590215425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542139061426409726810283 2313208592139614590215425)
                ·
                  refine ⟨1734906444104710942661569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313208592139614590215425 1734906444104710942661569)
                  ·
                    refine ⟨1301179833078533206996177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1734906444104710942661569 1301179833078533206996177)
                    ·
                      refine ⟨975884874808899905247133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301179833078533206996177 975884874808899905247133)
                      ·
                        rfl

theorem cell23_1900529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_1900529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900529 prefixEnd_1900529 := by exact prefixLift 1900529
  have htrace : WordTrace (prefixWord ++ tailWord_1900529) baseStart_1900529 baseEnd_1900529 := by
    simpa [prefixWord, tailWord_1900529, baseEnd_1900529] using wordTrace_append hprefix tailTrace_1900529
  have hstable : (prefixWord ++ tailWord_1900529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900529).length < 2 ^ (prefixWord ++ tailWord_1900529).sum := by decide
  have hdescent : baseEnd_1900529 < baseStart_1900529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900551 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1900551 : Nat := 118140960795 + 1900551 * 2 ^ 59
def prefixEnd_1900551 : Nat := 4983230072969 + 3 ^ 40 * 1900551 * 2
def baseEnd_1900551 : Nat := 975896171383298819172031

theorem tailTrace_1900551 : CollatzResearch.WordTrace tailWord_1900551 prefixEnd_1900551 975896171383298819172031 := by
  unfold tailWord_1900551
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318789737635790114117507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46212526491757193409411671 69318789737635790114117507)
  ·
    refine ⟨103978184606453685171176261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69318789737635790114117507 103978184606453685171176261)
    ·
      refine ⟨19495909613710065969595549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103978184606453685171176261 19495909613710065969595549)
      ·
        refine ⟨7310966105141274738598331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19495909613710065969595549 7310966105141274738598331)
        ·
          refine ⟨10966449157711912107897497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310966105141274738598331 10966449157711912107897497)
          ·
            refine ⟨8224836868283934080923123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10966449157711912107897497 8224836868283934080923123)
            ·
              refine ⟨12337255302425901121384685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224836868283934080923123 12337255302425901121384685)
              ·
                refine ⟨4626470738409712920519257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12337255302425901121384685 4626470738409712920519257)
                ·
                  refine ⟨3469853053807284690389443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4626470738409712920519257 3469853053807284690389443)
                  ·
                    refine ⟨5204779580710927035584165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3469853053807284690389443 5204779580710927035584165)
                    ·
                      refine ⟨975896171383298819172031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5204779580710927035584165 975896171383298819172031)
                      ·
                        rfl

theorem cell23_1900551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1900551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900551 prefixEnd_1900551 := by exact prefixLift 1900551
  have htrace : WordTrace (prefixWord ++ tailWord_1900551) baseStart_1900551 baseEnd_1900551 := by
    simpa [prefixWord, tailWord_1900551, baseEnd_1900551] using wordTrace_append hprefix tailTrace_1900551
  have hstable : (prefixWord ++ tailWord_1900551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900551).length < 2 ^ (prefixWord ++ tailWord_1900551).sum := by decide
  have hdescent : baseEnd_1900551 < baseStart_1900551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900628 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_1900628 : Nat := 118140960795 + 1900628 * 2 ^ 59
def prefixEnd_1900628 : Nat := 4983230072969 + 3 ^ 40 * 1900628 * 2
def baseEnd_1900628 : Nat := 975935709393695017909177

theorem tailTrace_1900628 : CollatzResearch.WordTrace tailWord_1900628 prefixEnd_1900628 975935709393695017909177 := by
  unfold tailWord_1900628
  simp only [CollatzResearch.WordTrace]
  refine ⟨34660799079178416132335269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46214398772237888176447025 34660799079178416132335269)
  ·
    refine ⟨6498899827345953024812863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34660799079178416132335269 6498899827345953024812863)
    ·
      refine ⟨9748349741018929537219295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498899827345953024812863 9748349741018929537219295)
      ·
        refine ⟨14622524611528394305828943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748349741018929537219295 14622524611528394305828943)
        ·
          refine ⟨21933786917292591458743415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14622524611528394305828943 21933786917292591458743415)
          ·
            refine ⟨32900680375938887188115123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21933786917292591458743415 32900680375938887188115123)
            ·
              refine ⟨49351020563908330782172685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32900680375938887188115123 49351020563908330782172685)
              ·
                refine ⟨18506632711465624043314757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49351020563908330782172685 18506632711465624043314757)
                ·
                  refine ⟨3469993633399804508121517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18506632711465624043314757 3469993633399804508121517)
                  ·
                    refine ⟨1301247612524926690545569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3469993633399804508121517 1301247612524926690545569)
                    ·
                      refine ⟨975935709393695017909177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301247612524926690545569 975935709393695017909177)
                      ·
                        rfl

theorem cell23_1900628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_1900628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900628 prefixEnd_1900628 := by exact prefixLift 1900628
  have htrace : WordTrace (prefixWord ++ tailWord_1900628) baseStart_1900628 baseEnd_1900628 := by
    simpa [prefixWord, tailWord_1900628, baseEnd_1900628] using wordTrace_append hprefix tailTrace_1900628
  have hstable : (prefixWord ++ tailWord_1900628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900628).length < 2 ^ (prefixWord ++ tailWord_1900628).sum := by decide
  have hdescent : baseEnd_1900628 < baseStart_1900628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900658 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1900658 : Nat := 118140960795 + 1900658 * 2 ^ 59
def prefixEnd_1900658 : Nat := 4983230072969 + 3 ^ 40 * 1900658 * 2
def baseEnd_1900658 : Nat := 975951113813329900534039

theorem tailTrace_1900658 : CollatzResearch.WordTrace tailWord_1900658 prefixEnd_1900658 975951113813329900534039 := by
  unfold tailWord_1900658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330673087062036847065657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46215128232165431592175085 17330673087062036847065657)
  ·
    refine ⟨12998004815296527635299243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17330673087062036847065657 12998004815296527635299243)
    ·
      refine ⟨19497007222944791452948865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12998004815296527635299243 19497007222944791452948865)
      ·
        refine ⟨14622755417208593589711649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19497007222944791452948865 14622755417208593589711649)
        ·
          refine ⟨10967066562906445192283737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14622755417208593589711649 10967066562906445192283737)
          ·
            refine ⟨8225299922179833894212803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10967066562906445192283737 8225299922179833894212803)
            ·
              refine ⟨12337949883269750841319205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225299922179833894212803 12337949883269750841319205)
              ·
                refine ⟨2313365603113078282747351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12337949883269750841319205 2313365603113078282747351)
                ·
                  refine ⟨3470048404669617424121027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313365603113078282747351 3470048404669617424121027)
                  ·
                    refine ⟨5205072607004426136181541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470048404669617424121027 5205072607004426136181541)
                    ·
                      refine ⟨975951113813329900534039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5205072607004426136181541 975951113813329900534039)
                      ·
                        rfl

theorem cell23_1900658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1900658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900658 prefixEnd_1900658 := by exact prefixLift 1900658
  have htrace : WordTrace (prefixWord ++ tailWord_1900658) baseStart_1900658 baseEnd_1900658 := by
    simpa [prefixWord, tailWord_1900658, baseEnd_1900658] using wordTrace_append hprefix tailTrace_1900658
  have hstable : (prefixWord ++ tailWord_1900658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900658).length < 2 ^ (prefixWord ++ tailWord_1900658).sum := by decide
  have hdescent : baseEnd_1900658 < baseStart_1900658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900698 : List Nat := [3, 1, 1, 5, 2, 1, 2, 8]
def baseStart_1900698 : Nat := 118140960795 + 1900698 * 2 ^ 59
def prefixEnd_1900698 : Nat := 4983230072969 + 3 ^ 40 * 1900698 * 2
def baseEnd_1900698 : Nat := 36147098260722583112365

theorem tailTrace_1900698 : CollatzResearch.WordTrace tailWord_1900698 prefixEnd_1900698 36147098260722583112365 := by
  unfold tailWord_1900698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331037817025808554929687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46216100845402156146479165 17331037817025808554929687)
  ·
    refine ⟨25996556725538712832394531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17331037817025808554929687 25996556725538712832394531)
    ·
      refine ⟨38994835088308069248591797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25996556725538712832394531 38994835088308069248591797)
      ·
        refine ⟨3655765789528881492055481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38994835088308069248591797 3655765789528881492055481)
        ·
          refine ⟨2741824342146661119041611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3655765789528881492055481 2741824342146661119041611)
          ·
            refine ⟨4112736513219991678562417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741824342146661119041611 4112736513219991678562417)
            ·
              refine ⟨3084552384914993758921813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112736513219991678562417 3084552384914993758921813)
              ·
                refine ⟨36147098260722583112365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3084552384914993758921813 36147098260722583112365)
                ·
                  rfl

theorem cell23_1900698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_1900698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900698 prefixEnd_1900698 := by exact prefixLift 1900698
  have htrace : WordTrace (prefixWord ++ tailWord_1900698) baseStart_1900698 baseEnd_1900698 := by
    simpa [prefixWord, tailWord_1900698, baseEnd_1900698] using wordTrace_append hprefix tailTrace_1900698
  have hstable : (prefixWord ++ tailWord_1900698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900698).length < 2 ^ (prefixWord ++ tailWord_1900698).sum := by decide
  have hdescent : baseEnd_1900698 < baseStart_1900698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900702 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1900702 : Nat := 118140960795 + 1900702 * 2 ^ 59
def prefixEnd_1900702 : Nat := 4983230072969 + 3 ^ 40 * 1900702 * 2
def baseEnd_1900702 : Nat := 325324568987375909461279

theorem tailTrace_1900702 : CollatzResearch.WordTrace tailWord_1900702 prefixEnd_1900702 325324568987375909461279 := by
  unfold tailWord_1900702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8665537145011092862858045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46216198106725828601909573 8665537145011092862858045)
  ·
    refine ⟨3249576429379159823571767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8665537145011092862858045 3249576429379159823571767)
    ·
      refine ⟨4874364644068739735357651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249576429379159823571767 4874364644068739735357651)
      ·
        refine ⟨7311546966103109603036477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874364644068739735357651 7311546966103109603036477)
        ·
          refine ⟨2741830112288666101138679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7311546966103109603036477 2741830112288666101138679)
          ·
            refine ⟨4112745168432999151708019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741830112288666101138679 4112745168432999151708019)
            ·
              refine ⟨6169117752649498727562029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4112745168432999151708019 6169117752649498727562029)
              ·
                refine ⟨2313419157243562022835761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6169117752649498727562029 2313419157243562022835761)
                ·
                  refine ⟨1735064367932671517126821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313419157243562022835761 1735064367932671517126821)
                  ·
                    refine ⟨325324568987375909461279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735064367932671517126821 325324568987375909461279)
                    ·
                      rfl

theorem cell23_1900702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1900702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900702 prefixEnd_1900702 := by exact prefixLift 1900702
  have htrace : WordTrace (prefixWord ++ tailWord_1900702) baseStart_1900702 baseEnd_1900702 := by
    simpa [prefixWord, tailWord_1900702, baseEnd_1900702] using wordTrace_append hprefix tailTrace_1900702
  have hstable : (prefixWord ++ tailWord_1900702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900702).length < 2 ^ (prefixWord ++ tailWord_1900702).sum := by decide
  have hdescent : baseEnd_1900702 < baseStart_1900702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900751 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_1900751 : Nat := 118140960795 + 1900751 * 2 ^ 59
def prefixEnd_1900751 : Nat := 4983230072969 + 3 ^ 40 * 1900751 * 2
def baseEnd_1900751 : Nat := 975998867514198036671111

theorem tailTrace_1900751 : CollatzResearch.WordTrace tailWord_1900751 prefixEnd_1900751 975998867514198036671111 := by
  unfold tailWord_1900751
  simp only [CollatzResearch.WordTrace]
  refine ⟨69326084336911224271398107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46217389557940816180932071 69326084336911224271398107)
  ·
    refine ⟨103989126505366836407097161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69326084336911224271398107 103989126505366836407097161)
    ·
      refine ⟨77991844879025127305322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103989126505366836407097161 77991844879025127305322871)
      ·
        refine ⟨116987767318537690957984307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77991844879025127305322871 116987767318537690957984307)
        ·
          refine ⟨175481650977806536436976461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116987767318537690957984307 175481650977806536436976461)
          ·
            refine ⟨65805619116677451163866173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175481650977806536436976461 65805619116677451163866173)
            ·
              refine ⟨24677107168754044186449815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65805619116677451163866173 24677107168754044186449815)
              ·
                refine ⟨37015660753131066279674723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24677107168754044186449815 37015660753131066279674723)
                ·
                  refine ⟨55523491129696599419512085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37015660753131066279674723 55523491129696599419512085)
                  ·
                    refine ⟨2602663646704528097789629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55523491129696599419512085 2602663646704528097789629)
                    ·
                      refine ⟨975998867514198036671111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2602663646704528097789629 975998867514198036671111)
                      ·
                        rfl

theorem cell23_1900751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_1900751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900751 prefixEnd_1900751 := by exact prefixLift 1900751
  have htrace : WordTrace (prefixWord ++ tailWord_1900751) baseStart_1900751 baseEnd_1900751 := by
    simpa [prefixWord, tailWord_1900751, baseEnd_1900751] using wordTrace_append hprefix tailTrace_1900751
  have hstable : (prefixWord ++ tailWord_1900751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900751).length < 2 ^ (prefixWord ++ tailWord_1900751).sum := by decide
  have hdescent : baseEnd_1900751 < baseStart_1900751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900761 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1900761 : Nat := 118140960795 + 1900761 * 2 ^ 59
def prefixEnd_1900761 : Nat := 4983230072969 + 3 ^ 40 * 1900761 * 2
def baseEnd_1900761 : Nat := 976004002320742997546065

theorem tailTrace_1900761 : CollatzResearch.WordTrace tailWord_1900761 prefixEnd_1900761 976004002320742997546065 := by
  unfold tailWord_1900761
  simp only [CollatzResearch.WordTrace]
  refine ⟨69326449066874995979262137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46217632711249997319508091 69326449066874995979262137)
  ·
    refine ⟨51994836800156246984446603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69326449066874995979262137 51994836800156246984446603)
    ·
      refine ⟨77992255200234370476669905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51994836800156246984446603 77992255200234370476669905)
      ·
        refine ⟨58494191400175777857502429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77992255200234370476669905 58494191400175777857502429)
        ·
          refine ⟨21935321775065916696563411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58494191400175777857502429 21935321775065916696563411)
          ·
            refine ⟨32902982662598875044845117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21935321775065916696563411 32902982662598875044845117)
            ·
              refine ⟨12338618498474578141816919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32902982662598875044845117 12338618498474578141816919)
              ·
                refine ⟨18507927747711867212725379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338618498474578141816919 18507927747711867212725379)
                ·
                  refine ⟨27761891621567800819088069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18507927747711867212725379 27761891621567800819088069)
                  ·
                    refine ⟨5205354679043962653579013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27761891621567800819088069 5205354679043962653579013)
                    ·
                      refine ⟨976004002320742997546065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5205354679043962653579013 976004002320742997546065)
                      ·
                        rfl

theorem cell23_1900761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1900761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900761 prefixEnd_1900761 := by exact prefixLift 1900761
  have htrace : WordTrace (prefixWord ++ tailWord_1900761) baseStart_1900761 baseEnd_1900761 := by
    simpa [prefixWord, tailWord_1900761, baseEnd_1900761] using wordTrace_append hprefix tailTrace_1900761
  have hstable : (prefixWord ++ tailWord_1900761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900761).length < 2 ^ (prefixWord ++ tailWord_1900761).sum := by decide
  have hdescent : baseEnd_1900761 < baseStart_1900761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900811 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_1900811 : Nat := 118140960795 + 1900811 * 2 ^ 59
def prefixEnd_1900811 : Nat := 4983230072969 + 3 ^ 40 * 1900811 * 2
def baseEnd_1900811 : Nat := 976029676353467801920835

theorem tailTrace_1900811 : CollatzResearch.WordTrace tailWord_1900811 prefixEnd_1900811 976029676353467801920835 := by
  unfold tailWord_1900811
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328272716693854518582287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46218848477795903012388191 69328272716693854518582287)
  ·
    refine ⟨103992409075040781777873431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69328272716693854518582287 103992409075040781777873431)
    ·
      refine ⟨155988613612561172666810147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103992409075040781777873431 155988613612561172666810147)
      ·
        refine ⟨233982920418841759000215221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155988613612561172666810147 233982920418841759000215221)
        ·
          refine ⟨21935898789266414906270177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233982920418841759000215221 21935898789266414906270177)
          ·
            refine ⟨16451924091949811179702633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21935898789266414906270177 16451924091949811179702633)
            ·
              refine ⟨12338943068962358384776975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16451924091949811179702633 12338943068962358384776975)
              ·
                refine ⟨18508414603443537577165463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338943068962358384776975 18508414603443537577165463)
                ·
                  refine ⟨27762621905165306365748195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18508414603443537577165463 27762621905165306365748195)
                  ·
                    refine ⟨41643932857747959548622293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27762621905165306365748195 41643932857747959548622293)
                    ·
                      refine ⟨976029676353467801920835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41643932857747959548622293 976029676353467801920835)
                      ·
                        rfl

theorem cell23_1900811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_1900811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900811 prefixEnd_1900811 := by exact prefixLift 1900811
  have htrace : WordTrace (prefixWord ++ tailWord_1900811) baseStart_1900811 baseEnd_1900811 := by
    simpa [prefixWord, tailWord_1900811, baseEnd_1900811] using wordTrace_append hprefix tailTrace_1900811
  have hstable : (prefixWord ++ tailWord_1900811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900811).length < 2 ^ (prefixWord ++ tailWord_1900811).sum := by decide
  have hdescent : baseEnd_1900811 < baseStart_1900811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900950 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1900950 : Nat := 118140960795 + 1900950 * 2 ^ 59
def prefixEnd_1900950 : Nat := 4983230072969 + 3 ^ 40 * 1900950 * 2
def baseEnd_1900950 : Nat := 325367016721480919360899

theorem tailTrace_1900950 : CollatzResearch.WordTrace tailWord_1900950 prefixEnd_1900950 325367016721480919360899 := by
  unfold tailWord_1900950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333333903949392578618269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46222228308793520838594869 4333333903949392578618269)
  ·
    refine ⟨1625000213981022216981851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4333333903949392578618269 1625000213981022216981851)
    ·
      refine ⟨2437500320971533325472777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625000213981022216981851 2437500320971533325472777)
      ·
        refine ⟨1828125240728649994104583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2437500320971533325472777 1828125240728649994104583)
        ·
          refine ⟨2742187861092974991156875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1828125240728649994104583 2742187861092974991156875)
          ·
            refine ⟨4113281791639462486735313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742187861092974991156875 4113281791639462486735313)
            ·
              refine ⟨3084961343729596865051485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113281791639462486735313 3084961343729596865051485)
              ·
                refine ⟨1156860503898598824394307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084961343729596865051485 1156860503898598824394307)
                ·
                  refine ⟨1735290755847898236591461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156860503898598824394307 1735290755847898236591461)
                  ·
                    refine ⟨325367016721480919360899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735290755847898236591461 325367016721480919360899)
                    ·
                      rfl

theorem cell23_1900950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1900950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900950 prefixEnd_1900950 := by exact prefixLift 1900950
  have htrace : WordTrace (prefixWord ++ tailWord_1900950) baseStart_1900950 baseEnd_1900950 := by
    simpa [prefixWord, tailWord_1900950, baseEnd_1900950] using wordTrace_append hprefix tailTrace_1900950
  have hstable : (prefixWord ++ tailWord_1900950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900950).length < 2 ^ (prefixWord ++ tailWord_1900950).sum := by decide
  have hdescent : baseEnd_1900950 < baseStart_1900950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900962 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1900962 : Nat := 118140960795 + 1900962 * 2 ^ 59
def prefixEnd_1900962 : Nat := 4983230072969 + 3 ^ 40 * 1900962 * 2
def baseEnd_1900962 : Nat := 976107211932296711132641

theorem tailTrace_1900962 : CollatzResearch.WordTrace tailWord_1900962 prefixEnd_1900962 976107211932296711132641 := by
  unfold tailWord_1900962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17333445034786701826832285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46222520092764538204886093 17333445034786701826832285)
  ·
    refine ⟨6500041888045013185062107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17333445034786701826832285 6500041888045013185062107)
    ·
      refine ⟨9750062832067519777593161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6500041888045013185062107 9750062832067519777593161)
      ·
        refine ⟨7312547124050639833194871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750062832067519777593161 7312547124050639833194871)
        ·
          refine ⟨10968820686075959749792307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312547124050639833194871 10968820686075959749792307)
          ·
            refine ⟨16453231029113939624688461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10968820686075959749792307 16453231029113939624688461)
            ·
              refine ⟨6169961635917727359258173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16453231029113939624688461 6169961635917727359258173)
              ·
                refine ⟨2313735613469147759721815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6169961635917727359258173 2313735613469147759721815)
                ·
                  refine ⟨3470603420203721639582723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313735613469147759721815 3470603420203721639582723)
                  ·
                    refine ⟨5205905130305582459374085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3470603420203721639582723 5205905130305582459374085)
                    ·
                      refine ⟨976107211932296711132641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5205905130305582459374085 976107211932296711132641)
                      ·
                        rfl

theorem cell23_1900962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1900962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900962 prefixEnd_1900962 := by exact prefixLift 1900962
  have htrace : WordTrace (prefixWord ++ tailWord_1900962) baseStart_1900962 baseEnd_1900962 := by
    simpa [prefixWord, tailWord_1900962, baseEnd_1900962] using wordTrace_append hprefix tailTrace_1900962
  have hstable : (prefixWord ++ tailWord_1900962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900962).length < 2 ^ (prefixWord ++ tailWord_1900962).sum := by decide
  have hdescent : baseEnd_1900962 < baseStart_1900962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900989 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1900989 : Nat := 118140960795 + 1900989 * 2 ^ 59
def prefixEnd_1900989 : Nat := 4983230072969 + 3 ^ 40 * 1900989 * 2
def baseEnd_1900989 : Nat := 325373691969989368498339

theorem tailTrace_1900989 : CollatzResearch.WordTrace tailWord_1900989 prefixEnd_1900989 325373691969989368498339 := by
  unfold tailWord_1900989
  simp only [CollatzResearch.WordTrace]
  refine ⟨69334764910048990918562021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46223176606699327279041347 69334764910048990918562021)
  ·
    refine ⟨13000268420634185797230379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69334764910048990918562021 13000268420634185797230379)
    ·
      refine ⟨19500402630951278695845569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000268420634185797230379 19500402630951278695845569)
      ·
        refine ⟨14625301973213459021884177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19500402630951278695845569 14625301973213459021884177)
        ·
          refine ⟨10968976479910094266413133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14625301973213459021884177 10968976479910094266413133)
          ·
            refine ⟨4113366179966285349904925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10968976479910094266413133 4113366179966285349904925)
            ·
              refine ⟨1542512317487357006214347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4113366179966285349904925 1542512317487357006214347)
              ·
                refine ⟨2313768476231035509321521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542512317487357006214347 2313768476231035509321521)
                ·
                  refine ⟨1735326357173276631991141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2313768476231035509321521 1735326357173276631991141)
                  ·
                    refine ⟨325373691969989368498339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735326357173276631991141 325373691969989368498339)
                    ·
                      rfl

theorem cell23_1900989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1900989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1900989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1900989 prefixEnd_1900989 := by exact prefixLift 1900989
  have htrace : WordTrace (prefixWord ++ tailWord_1900989) baseStart_1900989 baseEnd_1900989 := by
    simpa [prefixWord, tailWord_1900989, baseEnd_1900989] using wordTrace_append hprefix tailTrace_1900989
  have hstable : (prefixWord ++ tailWord_1900989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900989).length < 2 ^ (prefixWord ++ tailWord_1900989).sum := by decide
  have hdescent : baseEnd_1900989 < baseStart_1900989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901013 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1901013 : Nat := 118140960795 + 1901013 * 2 ^ 59
def prefixEnd_1901013 : Nat := 4983230072969 + 3 ^ 40 * 1901013 * 2
def baseEnd_1901013 : Nat := 976133399445676011594907

theorem tailTrace_1901013 : CollatzResearch.WordTrace tailWord_1901013 prefixEnd_1901013 976133399445676011594907 := by
  unfold tailWord_1901013
  simp only [CollatzResearch.WordTrace]
  refine ⟨69335640261962043017435693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46223760174641362011623795 69335640261962043017435693)
  ·
    refine ⟨26000865098235766131538385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69335640261962043017435693 26000865098235766131538385)
    ·
      refine ⟨19500648823676824598653789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26000865098235766131538385 19500648823676824598653789)
      ·
        refine ⟨7312743308878809224495171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19500648823676824598653789 7312743308878809224495171)
        ·
          refine ⟨10969114963318213836742757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312743308878809224495171 10969114963318213836742757)
          ·
            refine ⟨2056709055622165094389267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10969114963318213836742757 2056709055622165094389267)
            ·
              refine ⟨3085063583433247641583901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056709055622165094389267 3085063583433247641583901)
              ·
                refine ⟨1156898843787467865593963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3085063583433247641583901 1156898843787467865593963)
                ·
                  refine ⟨1735348265681201798390945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156898843787467865593963 1735348265681201798390945)
                  ·
                    refine ⟨1301511199260901348793209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735348265681201798390945 1301511199260901348793209)
                    ·
                      refine ⟨976133399445676011594907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301511199260901348793209 976133399445676011594907)
                      ·
                        rfl

theorem cell23_1901013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1901013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901013 prefixEnd_1901013 := by exact prefixLift 1901013
  have htrace : WordTrace (prefixWord ++ tailWord_1901013) baseStart_1901013 baseEnd_1901013 := by
    simpa [prefixWord, tailWord_1901013, baseEnd_1901013] using wordTrace_append hprefix tailTrace_1901013
  have hstable : (prefixWord ++ tailWord_1901013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901013).length < 2 ^ (prefixWord ++ tailWord_1901013).sum := by decide
  have hdescent : baseEnd_1901013 < baseStart_1901013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901052 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_1901052 : Nat := 118140960795 + 1901052 * 2 ^ 59
def prefixEnd_1901052 : Nat := 4983230072969 + 3 ^ 40 * 1901052 * 2
def baseEnd_1901052 : Nat := 976153425191201359007227

theorem tailTrace_1901052 : CollatzResearch.WordTrace tailWord_1901052 prefixEnd_1901052 976153425191201359007227 := by
  unfold tailWord_1901052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34668531354410376339052705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46224708472547168452070273 34668531354410376339052705)
  ·
    refine ⟨26001398515807782254289529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34668531354410376339052705 26001398515807782254289529)
    ·
      refine ⟨19501048886855836690717147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26001398515807782254289529 19501048886855836690717147)
      ·
        refine ⟨29251573330283755036075721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19501048886855836690717147 29251573330283755036075721)
        ·
          refine ⟨21938679997712816277056791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29251573330283755036075721 21938679997712816277056791)
          ·
            refine ⟨32908019996569224415585187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21938679997712816277056791 32908019996569224415585187)
            ·
              refine ⟨49362029994853836623377781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32908019996569224415585187 49362029994853836623377781)
              ·
                refine ⟨4627690312017547183441667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49362029994853836623377781 4627690312017547183441667)
                ·
                  refine ⟨6941535468026320775162501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627690312017547183441667 6941535468026320775162501)
                  ·
                    refine ⟨1301537900254935145342969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941535468026320775162501 1301537900254935145342969)
                    ·
                      refine ⟨976153425191201359007227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301537900254935145342969 976153425191201359007227)
                      ·
                        rfl

theorem cell23_1901052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_1901052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901052 prefixEnd_1901052 := by exact prefixLift 1901052
  have htrace : WordTrace (prefixWord ++ tailWord_1901052) baseStart_1901052 baseEnd_1901052 := by
    simpa [prefixWord, tailWord_1901052, baseEnd_1901052] using wordTrace_append hprefix tailTrace_1901052
  have hstable : (prefixWord ++ tailWord_1901052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901052).length < 2 ^ (prefixWord ++ tailWord_1901052).sum := by decide
  have hdescent : baseEnd_1901052 < baseStart_1901052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901105 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_1901105 : Nat := 118140960795 + 1901105 * 2 ^ 59
def prefixEnd_1901105 : Nat := 4983230072969 + 3 ^ 40 * 1901105 * 2
def baseEnd_1901105 : Nat := 325393546555296550548161

theorem tailTrace_1901105 : CollatzResearch.WordTrace tailWord_1901105 prefixEnd_1901105 325393546555296550548161 := by
  unfold tailWord_1901105
  simp only [CollatzResearch.WordTrace]
  refine ⟨69338995777628742729784769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46225997185085828486523179 69338995777628742729784769)
  ·
    refine ⟨52004246833221557047338577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69338995777628742729784769 52004246833221557047338577)
    ·
      refine ⟨39003185124916167785503933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52004246833221557047338577 39003185124916167785503933)
      ·
        refine ⟨14626194421843562919563975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39003185124916167785503933 14626194421843562919563975)
        ·
          refine ⟨21939291632765344379345963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14626194421843562919563975 21939291632765344379345963)
          ·
            refine ⟨32908937449148016569018945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21939291632765344379345963 32908937449148016569018945)
            ·
              refine ⟨24681703086861012426764209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32908937449148016569018945 24681703086861012426764209)
              ·
                refine ⟨18511277315145759320073157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24681703086861012426764209 18511277315145759320073157)
                ·
                  refine ⟨3470864496589829872513717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18511277315145759320073157 3470864496589829872513717)
                  ·
                    refine ⟨325393546555296550548161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3470864496589829872513717 325393546555296550548161)
                    ·
                      rfl

theorem cell23_1901105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_1901105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901105 prefixEnd_1901105 := by exact prefixLift 1901105
  have htrace : WordTrace (prefixWord ++ tailWord_1901105) baseStart_1901105 baseEnd_1901105 := by
    simpa [prefixWord, tailWord_1901105, baseEnd_1901105] using wordTrace_append hprefix tailTrace_1901105
  have hstable : (prefixWord ++ tailWord_1901105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901105).length < 2 ^ (prefixWord ++ tailWord_1901105).sum := by decide
  have hdescent : baseEnd_1901105 < baseStart_1901105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901112 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2]
def baseStart_1901112 : Nat := 118140960795 + 1901112 * 2 ^ 59
def prefixEnd_1901112 : Nat := 4983230072969 + 3 ^ 40 * 1901112 * 2
def baseEnd_1901112 : Nat := 976184234030471124256951

theorem tailTrace_1901112 : CollatzResearch.WordTrace tailWord_1901112 prefixEnd_1901112 976184234030471124256951 := by
  unfold tailWord_1901112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34669625544301691462644795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46226167392402255283526393 34669625544301691462644795)
  ·
    refine ⟨52004438316452537193967193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34669625544301691462644795 52004438316452537193967193)
    ·
      refine ⟨39003328737339402895475395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52004438316452537193967193 39003328737339402895475395)
      ·
        refine ⟨58504993106009104343213093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39003328737339402895475395 58504993106009104343213093)
        ·
          refine ⟨10969686207376707064352455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58504993106009104343213093 10969686207376707064352455)
          ·
            refine ⟨16454529311065060596528683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969686207376707064352455 16454529311065060596528683)
            ·
              refine ⟨24681793966597590894793025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16454529311065060596528683 24681793966597590894793025)
              ·
                refine ⟨18511345474948193171094769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24681793966597590894793025 18511345474948193171094769)
                ·
                  refine ⟨13883509106211144878321077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18511345474948193171094769 13883509106211144878321077)
                  ·
                    refine ⟨1301578978707294832342601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13883509106211144878321077 1301578978707294832342601)
                    ·
                      refine ⟨976184234030471124256951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301578978707294832342601 976184234030471124256951)
                      ·
                        rfl

theorem cell23_1901112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_1901112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901112 prefixEnd_1901112 := by exact prefixLift 1901112
  have htrace : WordTrace (prefixWord ++ tailWord_1901112) baseStart_1901112 baseEnd_1901112 := by
    simpa [prefixWord, tailWord_1901112, baseEnd_1901112] using wordTrace_append hprefix tailTrace_1901112
  have hstable : (prefixWord ++ tailWord_1901112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901112).length < 2 ^ (prefixWord ++ tailWord_1901112).sum := by decide
  have hdescent : baseEnd_1901112 < baseStart_1901112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901124 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1901124 : Nat := 118140960795 + 1901124 * 2 ^ 59
def prefixEnd_1901124 : Nat := 4983230072969 + 3 ^ 40 * 1901124 * 2
def baseEnd_1901124 : Nat := 976190395798325077306897

theorem tailTrace_1901124 : CollatzResearch.WordTrace tailWord_1901124 prefixEnd_1901124 976190395798325077306897 := by
  unfold tailWord_1901124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34669844382279954487363213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46226459176373272649817617 34669844382279954487363213)
  ·
    refine ⟨13001191643354982932761205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34669844382279954487363213 13001191643354982932761205)
    ·
      refine ⟨1218861716564529649946363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13001191643354982932761205 1218861716564529649946363)
      ·
        refine ⟨1828292574846794474919545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218861716564529649946363 1828292574846794474919545)
        ·
          refine ⟨1371219431135095856189659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1828292574846794474919545 1371219431135095856189659)
          ·
            refine ⟨2056829146702643784284489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371219431135095856189659 2056829146702643784284489)
            ·
              refine ⟨1542621860026982838213367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056829146702643784284489 1542621860026982838213367)
              ·
                refine ⟨2313932790040474257320051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542621860026982838213367 2313932790040474257320051)
                ·
                  refine ⟨3470899185060711385980077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313932790040474257320051 3470899185060711385980077)
                  ·
                    refine ⟨1301587194397766769742529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3470899185060711385980077 1301587194397766769742529)
                    ·
                      refine ⟨976190395798325077306897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301587194397766769742529 976190395798325077306897)
                      ·
                        rfl

theorem cell23_1901124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1901124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901124 prefixEnd_1901124 := by exact prefixLift 1901124
  have htrace : WordTrace (prefixWord ++ tailWord_1901124) baseStart_1901124 baseEnd_1901124 := by
    simpa [prefixWord, tailWord_1901124, baseEnd_1901124] using wordTrace_append hprefix tailTrace_1901124
  have hstable : (prefixWord ++ tailWord_1901124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901124).length < 2 ^ (prefixWord ++ tailWord_1901124).sum := by decide
  have hdescent : baseEnd_1901124 < baseStart_1901124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901126 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1901126 : Nat := 118140960795 + 1901126 * 2 ^ 59
def prefixEnd_1901126 : Nat := 4983230072969 + 3 ^ 40 * 1901126 * 2
def baseEnd_1901126 : Nat := 108465713639959341053543

theorem tailTrace_1901126 : CollatzResearch.WordTrace tailWord_1901126 prefixEnd_1901126 108465713639959341053543 := by
  unfold tailWord_1901126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166867553454770728634351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46226507807035108877532821 2166867553454770728634351)
  ·
    refine ⟨3250301330182156092951527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2166867553454770728634351 3250301330182156092951527)
    ·
      refine ⟨4875451995273234139427291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3250301330182156092951527 4875451995273234139427291)
      ·
        refine ⟨7313177992909851209140937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875451995273234139427291 7313177992909851209140937)
        ·
          refine ⟨5484883494682388406855703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313177992909851209140937 5484883494682388406855703)
          ·
            refine ⟨8227325242023582610283555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484883494682388406855703 8227325242023582610283555)
            ·
              refine ⟨12340987863035373915425333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227325242023582610283555 12340987863035373915425333)
              ·
                refine ⟨1156967612159566304571125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12340987863035373915425333 1156967612159566304571125)
                ·
                  refine ⟨108465713639959341053543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1156967612159566304571125 108465713639959341053543)
                  ·
                    rfl

theorem cell23_1901126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1901126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901126 prefixEnd_1901126 := by exact prefixLift 1901126
  have htrace : WordTrace (prefixWord ++ tailWord_1901126) baseStart_1901126 baseEnd_1901126 := by
    simpa [prefixWord, tailWord_1901126, baseEnd_1901126] using wordTrace_append hprefix tailTrace_1901126
  have hstable : (prefixWord ++ tailWord_1901126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901126).length < 2 ^ (prefixWord ++ tailWord_1901126).sum := by decide
  have hdescent : baseEnd_1901126 < baseStart_1901126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901152 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_1901152 : Nat := 118140960795 + 1901152 * 2 ^ 59
def prefixEnd_1901152 : Nat := 4983230072969 + 3 ^ 40 * 1901152 * 2
def baseEnd_1901152 : Nat := 325401591085550322585589

theorem tailTrace_1901152 : CollatzResearch.WordTrace tailWord_1901152 prefixEnd_1901152 325401591085550322585589 := by
  unfold tailWord_1901152
  simp only [CollatzResearch.WordTrace]
  refine ⟨34670355004229234878372855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46227140005638979837830473 34670355004229234878372855)
  ·
    refine ⟨52005532506343852317559283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34670355004229234878372855 52005532506343852317559283)
    ·
      refine ⟨78008298759515778476338925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52005532506343852317559283 78008298759515778476338925)
      ·
        refine ⟨29253112034818416928627097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78008298759515778476338925 29253112034818416928627097)
        ·
          refine ⟨21939834026113812696470323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29253112034818416928627097 21939834026113812696470323)
          ·
            refine ⟨32909751039170719044705485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21939834026113812696470323 32909751039170719044705485)
            ·
              refine ⟨12341156639689019641764557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32909751039170719044705485 12341156639689019641764557)
              ·
                refine ⟨4627933739883382365661709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12341156639689019641764557 4627933739883382365661709)
                ·
                  refine ⟨1735475152456268387123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4627933739883382365661709 1735475152456268387123141)
                  ·
                    refine ⟨325401591085550322585589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735475152456268387123141 325401591085550322585589)
                    ·
                      rfl

theorem cell23_1901152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_1901152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901152 prefixEnd_1901152 := by exact prefixLift 1901152
  have htrace : WordTrace (prefixWord ++ tailWord_1901152) baseStart_1901152 baseEnd_1901152 := by
    simpa [prefixWord, tailWord_1901152, baseEnd_1901152] using wordTrace_append hprefix tailTrace_1901152
  have hstable : (prefixWord ++ tailWord_1901152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901152).length < 2 ^ (prefixWord ++ tailWord_1901152).sum := by decide
  have hdescent : baseEnd_1901152 < baseStart_1901152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901155 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1901155 : Nat := 118140960795 + 1901155 * 2 ^ 59
def prefixEnd_1901155 : Nat := 4983230072969 + 3 ^ 40 * 1901155 * 2
def baseEnd_1901155 : Nat := 976206313698614456019253

theorem tailTrace_1901155 : CollatzResearch.WordTrace tailWord_1901155 prefixEnd_1901155 976206313698614456019253 := by
  unfold tailWord_1901155
  simp only [CollatzResearch.WordTrace]
  refine ⟨69340819427447601269104919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46227212951631734179403279 69340819427447601269104919)
  ·
    refine ⟨104011229141171401903657379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69340819427447601269104919 104011229141171401903657379)
    ·
      refine ⟨156016843711757102855486069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104011229141171401903657379 156016843711757102855486069)
      ·
        refine ⟨14626579097977228392701819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156016843711757102855486069 14626579097977228392701819)
        ·
          refine ⟨21939868646965842589052729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14626579097977228392701819 21939868646965842589052729)
          ·
            refine ⟨16454901485224381941789547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21939868646965842589052729 16454901485224381941789547)
            ·
              refine ⟨24682352227836572912684321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16454901485224381941789547 24682352227836572912684321)
              ·
                refine ⟨18511764170877429684513241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24682352227836572912684321 18511764170877429684513241)
                ·
                  refine ⟨13883823128158072263384931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18511764170877429684513241 13883823128158072263384931)
                  ·
                    refine ⟨20825734692237108395077397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13883823128158072263384931 20825734692237108395077397)
                    ·
                      refine ⟨976206313698614456019253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20825734692237108395077397 976206313698614456019253)
                      ·
                        rfl

theorem cell23_1901155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1901155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901155 prefixEnd_1901155 := by exact prefixLift 1901155
  have htrace : WordTrace (prefixWord ++ tailWord_1901155) baseStart_1901155 baseEnd_1901155 := by
    simpa [prefixWord, tailWord_1901155, baseEnd_1901155] using wordTrace_append hprefix tailTrace_1901155
  have hstable : (prefixWord ++ tailWord_1901155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901155).length < 2 ^ (prefixWord ++ tailWord_1901155).sum := by decide
  have hdescent : baseEnd_1901155 < baseStart_1901155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901162 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1901162 : Nat := 118140960795 + 1901162 * 2 ^ 59
def prefixEnd_1901162 : Nat := 4983230072969 + 3 ^ 40 * 1901162 * 2
def baseEnd_1901162 : Nat := 976209908063195928631721

theorem tailTrace_1901162 : CollatzResearch.WordTrace tailWord_1901162 prefixEnd_1901162 976209908063195928631721 := by
  unfold tailWord_1901162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335268684605560366152435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46227383158948160976406493 17335268684605560366152435)
  ·
    refine ⟨26002903026908340549228653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17335268684605560366152435 26002903026908340549228653)
    ·
      refine ⟨9751088635090627705960745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26002903026908340549228653 9751088635090627705960745)
      ·
        refine ⟨7313316476317970779470559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9751088635090627705960745 7313316476317970779470559)
        ·
          refine ⟨10969974714476956169205839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313316476317970779470559 10969974714476956169205839)
          ·
            refine ⟨16454962071715434253808759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969974714476956169205839 16454962071715434253808759)
            ·
              refine ⟨24682443107573151380713139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16454962071715434253808759 24682443107573151380713139)
              ·
                refine ⟨37023664661359727071069709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24682443107573151380713139 37023664661359727071069709)
                ·
                  refine ⟨13883874248009897651651141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37023664661359727071069709 13883874248009897651651141)
                  ·
                    refine ⟨2603226421501855809684589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13883874248009897651651141 2603226421501855809684589)
                    ·
                      refine ⟨976209908063195928631721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603226421501855809684589 976209908063195928631721)
                      ·
                        rfl

theorem cell23_1901162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1901162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901162 prefixEnd_1901162 := by exact prefixLift 1901162
  have htrace : WordTrace (prefixWord ++ tailWord_1901162) baseStart_1901162 baseEnd_1901162 := by
    simpa [prefixWord, tailWord_1901162, baseEnd_1901162] using wordTrace_append hprefix tailTrace_1901162
  have hstable : (prefixWord ++ tailWord_1901162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901162).length < 2 ^ (prefixWord ++ tailWord_1901162).sum := by decide
  have hdescent : baseEnd_1901162 < baseStart_1901162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901205 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1901205 : Nat := 118140960795 + 1901205 * 2 ^ 59
def prefixEnd_1901205 : Nat := 4983230072969 + 3 ^ 40 * 1901205 * 2
def baseEnd_1901205 : Nat := 976231987731339260394023

theorem tailTrace_1901205 : CollatzResearch.WordTrace tailWord_1901205 prefixEnd_1901205 976231987731339260394023 := by
  unfold tailWord_1901205
  simp only [CollatzResearch.WordTrace]
  refine ⟨69342643077266459808425069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46228428718177639872283379 69342643077266459808425069)
  ·
    refine ⟨26003491153974922428159401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69342643077266459808425069 26003491153974922428159401)
    ·
      refine ⟨19502618365481191821119551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26003491153974922428159401 19502618365481191821119551)
      ·
        refine ⟨29253927548221787731679327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19502618365481191821119551 29253927548221787731679327)
        ·
          refine ⟨43880891322332681597518991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29253927548221787731679327 43880891322332681597518991)
          ·
            refine ⟨65821336983499022396278487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43880891322332681597518991 65821336983499022396278487)
            ·
              refine ⟨98732005475248533594417731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65821336983499022396278487 98732005475248533594417731)
              ·
                refine ⟨148098008212872800391626597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98732005475248533594417731 148098008212872800391626597)
                ·
                  refine ⟨27768376539913650073429987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148098008212872800391626597 27768376539913650073429987)
                  ·
                    refine ⟨41652564809870475110144981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27768376539913650073429987 41652564809870475110144981)
                    ·
                      refine ⟨976231987731339260394023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41652564809870475110144981 976231987731339260394023)
                      ·
                        rfl

theorem cell23_1901205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1901205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901205 prefixEnd_1901205 := by exact prefixLift 1901205
  have htrace : WordTrace (prefixWord ++ tailWord_1901205) baseStart_1901205 baseEnd_1901205 := by
    simpa [prefixWord, tailWord_1901205, baseEnd_1901205] using wordTrace_append hprefix tailTrace_1901205
  have hstable : (prefixWord ++ tailWord_1901205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901205).length < 2 ^ (prefixWord ++ tailWord_1901205).sum := by decide
  have hdescent : baseEnd_1901205 < baseStart_1901205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901216 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 6]
def baseStart_1901216 : Nat := 118140960795 + 1901216 * 2 ^ 59
def prefixEnd_1901216 : Nat := 4983230072969 + 3 ^ 40 * 1901216 * 2
def baseEnd_1901216 : Nat := 108470848446504301928497

theorem tailTrace_1901216 : CollatzResearch.WordTrace tailWord_1901216 prefixEnd_1901216 108470848446504301928497 := by
  unfold tailWord_1901216
  simp only [CollatzResearch.WordTrace]
  refine ⟨34671522140113304343537751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46228696186817739124717001 34671522140113304343537751)
  ·
    refine ⟨52007283210169956515306627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34671522140113304343537751 52007283210169956515306627)
    ·
      refine ⟨78010924815254934772959941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52007283210169956515306627 78010924815254934772959941)
      ·
        refine ⟨14627048402860300269929989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78010924815254934772959941 14627048402860300269929989)
        ·
          refine ⟨2742571575536306300611873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14627048402860300269929989 2742571575536306300611873)
          ·
            refine ⟨2056928681652229725458905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742571575536306300611873 2056928681652229725458905)
            ·
              refine ⟨1542696511239172294094179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056928681652229725458905 1542696511239172294094179)
              ·
                refine ⟨2314044766858758441141269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542696511239172294094179 2314044766858758441141269)
                ·
                  refine ⟨108470848446504301928497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2314044766858758441141269 108470848446504301928497)
                  ·
                    rfl

theorem cell23_1901216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 6].length) (baseStart_1901216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901216 prefixEnd_1901216 := by exact prefixLift 1901216
  have htrace : WordTrace (prefixWord ++ tailWord_1901216) baseStart_1901216 baseEnd_1901216 := by
    simpa [prefixWord, tailWord_1901216, baseEnd_1901216] using wordTrace_append hprefix tailTrace_1901216
  have hstable : (prefixWord ++ tailWord_1901216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901216).length < 2 ^ (prefixWord ++ tailWord_1901216).sum := by decide
  have hdescent : baseEnd_1901216 < baseStart_1901216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901229 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1901229 : Nat := 118140960795 + 1901229 * 2 ^ 59
def prefixEnd_1901229 : Nat := 4983230072969 + 3 ^ 40 * 1901229 * 2
def baseEnd_1901229 : Nat := 325414770422349055497971

theorem tailTrace_1901229 : CollatzResearch.WordTrace tailWord_1901229 prefixEnd_1901229 325414770422349055497971 := by
  unfold tailWord_1901229
  simp only [CollatzResearch.WordTrace]
  refine ⟨69343518429179511907298741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46229012286119674604865827 69343518429179511907298741)
  ·
    refine ⟨6500954852735579241309257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69343518429179511907298741 6500954852735579241309257)
    ·
      refine ⟨4875716139551684430981943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6500954852735579241309257 4875716139551684430981943)
      ·
        refine ⟨7313574209327526646472915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4875716139551684430981943 7313574209327526646472915)
        ·
          refine ⟨10970361313991289969709373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313574209327526646472915 10970361313991289969709373)
          ·
            refine ⟨4113885492746733738641015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10970361313991289969709373 4113885492746733738641015)
            ·
              refine ⟨6170828239120100607961523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4113885492746733738641015 6170828239120100607961523)
              ·
                refine ⟨9256242358680150911942285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170828239120100607961523 9256242358680150911942285)
                ·
                  refine ⟨3471090884505056591978357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9256242358680150911942285 3471090884505056591978357)
                  ·
                    refine ⟨325414770422349055497971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3471090884505056591978357 325414770422349055497971)
                    ·
                      rfl

theorem cell23_1901229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1901229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901229 prefixEnd_1901229 := by exact prefixLift 1901229
  have htrace : WordTrace (prefixWord ++ tailWord_1901229) baseStart_1901229 baseEnd_1901229 := by
    simpa [prefixWord, tailWord_1901229, baseEnd_1901229] using wordTrace_append hprefix tailTrace_1901229
  have hstable : (prefixWord ++ tailWord_1901229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901229).length < 2 ^ (prefixWord ++ tailWord_1901229).sum := by decide
  have hdescent : baseEnd_1901229 < baseStart_1901229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901242 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_1901242 : Nat := 118140960795 + 1901242 * 2 ^ 59
def prefixEnd_1901242 : Nat := 4983230072969 + 3 ^ 40 * 1901242 * 2
def baseEnd_1901242 : Nat := 325416995505185205210451

theorem tailTrace_1901242 : CollatzResearch.WordTrace tailWord_1901242 prefixEnd_1901242 325416995505185205210451 := by
  unfold tailWord_1901242
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335998144533103781880495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46229328385421610085014653 17335998144533103781880495)
  ·
    refine ⟨26003997216799655672820743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17335998144533103781880495 26003997216799655672820743)
    ·
      refine ⟨39005995825199483509231115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26003997216799655672820743 39005995825199483509231115)
      ·
        refine ⟨58508993737799225263846673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39005995825199483509231115 58508993737799225263846673)
        ·
          refine ⟨43881745303349418947885005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58508993737799225263846673 43881745303349418947885005)
          ·
            refine ⟨16455654488756032105456877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43881745303349418947885005 16455654488756032105456877)
            ·
              refine ⟨6170870433283512039546329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16455654488756032105456877 6170870433283512039546329)
              ·
                refine ⟨4628152824962634029659747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170870433283512039546329 4628152824962634029659747)
                ·
                  refine ⟨6942229237443951044489621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628152824962634029659747 6942229237443951044489621)
                  ·
                    refine ⟨325416995505185205210451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6942229237443951044489621 325416995505185205210451)
                    ·
                      rfl

theorem cell23_1901242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_1901242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901242 prefixEnd_1901242 := by exact prefixLift 1901242
  have htrace : WordTrace (prefixWord ++ tailWord_1901242) baseStart_1901242 baseEnd_1901242 := by
    simpa [prefixWord, tailWord_1901242, baseEnd_1901242] using wordTrace_append hprefix tailTrace_1901242
  have hstable : (prefixWord ++ tailWord_1901242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901242).length < 2 ^ (prefixWord ++ tailWord_1901242).sum := by decide
  have hdescent : baseEnd_1901242 < baseStart_1901242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901246 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1901246 : Nat := 118140960795 + 1901246 * 2 ^ 59
def prefixEnd_1901246 : Nat := 4983230072969 + 3 ^ 40 * 1901246 * 2
def baseEnd_1901246 : Nat := 325417680146057866660445

theorem tailTrace_1901246 : CollatzResearch.WordTrace tailWord_1901246 prefixEnd_1901246 325417680146057866660445 := by
  unfold tailWord_1901246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668017308764740476333449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46229425646745282540445061 8668017308764740476333449)
  ·
    refine ⟨6501012981573555357250087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8668017308764740476333449 6501012981573555357250087)
    ·
      refine ⟨9751519472360333035875131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501012981573555357250087 9751519472360333035875131)
      ·
        refine ⟨14627279208540499553812697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751519472360333035875131 14627279208540499553812697)
        ·
          refine ⟨10970459406405374665359523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14627279208540499553812697 10970459406405374665359523)
          ·
            refine ⟨16455689109608061998039285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970459406405374665359523 16455689109608061998039285)
            ·
              refine ⟨1542720854025755812316183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16455689109608061998039285 1542720854025755812316183)
              ·
                refine ⟨2314081281038633718474275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542720854025755812316183 2314081281038633718474275)
                ·
                  refine ⟨3471121921557950577711413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314081281038633718474275 3471121921557950577711413)
                  ·
                    refine ⟨325417680146057866660445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3471121921557950577711413 325417680146057866660445)
                    ·
                      rfl

theorem cell23_1901246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1901246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901246 prefixEnd_1901246 := by exact prefixLift 1901246
  have htrace : WordTrace (prefixWord ++ tailWord_1901246) baseStart_1901246 baseEnd_1901246 := by
    simpa [prefixWord, tailWord_1901246, baseEnd_1901246] using wordTrace_append hprefix tailTrace_1901246
  have hstable : (prefixWord ++ tailWord_1901246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901246).length < 2 ^ (prefixWord ++ tailWord_1901246).sum := by decide
  have hdescent : baseEnd_1901246 < baseStart_1901246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901254 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1901254 : Nat := 118140960795 + 1901254 * 2 ^ 59
def prefixEnd_1901254 : Nat := 4983230072969 + 3 ^ 40 * 1901254 * 2
def baseEnd_1901254 : Nat := 325419049427803189560433

theorem tailTrace_1901254 : CollatzResearch.WordTrace tailWord_1901254 prefixEnd_1901254 325419049427803189560433 := by
  unfold tailWord_1901254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167013445440279411779963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46229620169392627451305877 2167013445440279411779963)
  ·
    refine ⟨3250520168160419117669945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2167013445440279411779963 3250520168160419117669945)
    ·
      refine ⟨2437890126120314338252459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3250520168160419117669945 2437890126120314338252459)
      ·
        refine ⟨3656835189180471507378689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437890126120314338252459 3656835189180471507378689)
        ·
          refine ⟨2742626391885353630534017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656835189180471507378689 2742626391885353630534017)
          ·
            refine ⟨2056969793914015222900513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742626391885353630534017 2056969793914015222900513)
            ·
              refine ⟨1542727345435511417175385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056969793914015222900513 1542727345435511417175385)
              ·
                refine ⟨1157045509076633562881539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542727345435511417175385 1157045509076633562881539)
                ·
                  refine ⟨1735568263614950344322309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157045509076633562881539 1735568263614950344322309)
                  ·
                    refine ⟨325419049427803189560433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735568263614950344322309 325419049427803189560433)
                    ·
                      rfl

theorem cell23_1901254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1901254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901254 prefixEnd_1901254 := by exact prefixLift 1901254
  have htrace : WordTrace (prefixWord ++ tailWord_1901254) baseStart_1901254 baseEnd_1901254 := by
    simpa [prefixWord, tailWord_1901254, baseEnd_1901254] using wordTrace_append hprefix tailTrace_1901254
  have hstable : (prefixWord ++ tailWord_1901254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901254).length < 2 ^ (prefixWord ++ tailWord_1901254).sum := by decide
  have hdescent : baseEnd_1901254 < baseStart_1901254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901260 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 1, 1, 3]
def baseStart_1901260 : Nat := 118140960795 + 1901260 * 2 ^ 59
def prefixEnd_1901260 : Nat := 4983230072969 + 3 ^ 40 * 1901260 * 2
def baseEnd_1901260 : Nat := 976260229167336545206271

theorem tailTrace_1901260 : CollatzResearch.WordTrace tailWord_1901260 prefixEnd_1901260 976260229167336545206271 := by
  unfold tailWord_1901260
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672324546033602100838617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46229766061378136134451489 34672324546033602100838617)
  ·
    refine ⟨26004243409525201575628963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34672324546033602100838617 26004243409525201575628963)
    ·
      refine ⟨39006365114287802363443445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26004243409525201575628963 39006365114287802363443445)
      ·
        refine ⟨3656846729464481471572823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39006365114287802363443445 3656846729464481471572823)
        ·
          refine ⟨5485270094196722207359235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656846729464481471572823 5485270094196722207359235)
          ·
            refine ⟨8227905141295083311038853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485270094196722207359235 8227905141295083311038853)
            ·
              refine ⟨1542732213992828120819785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8227905141295083311038853 1542732213992828120819785)
              ·
                refine ⟨1157049160494621090614839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542732213992828120819785 1157049160494621090614839)
                ·
                  refine ⟨1735573740741931635922259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157049160494621090614839 1735573740741931635922259)
                  ·
                    refine ⟨2603360611112897453883389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735573740741931635922259 2603360611112897453883389)
                    ·
                      refine ⟨976260229167336545206271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603360611112897453883389 976260229167336545206271)
                      ·
                        rfl

theorem cell23_1901260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_1901260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901260 prefixEnd_1901260 := by exact prefixLift 1901260
  have htrace : WordTrace (prefixWord ++ tailWord_1901260) baseStart_1901260 baseEnd_1901260 := by
    simpa [prefixWord, tailWord_1901260, baseEnd_1901260] using wordTrace_append hprefix tailTrace_1901260
  have hstable : (prefixWord ++ tailWord_1901260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901260).length < 2 ^ (prefixWord ++ tailWord_1901260).sum := by decide
  have hdescent : baseEnd_1901260 < baseStart_1901260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901272 : List Nat := [2, 1, 2, 2, 3, 2, 3, 8]
def baseStart_1901272 : Nat := 118140960795 + 1901272 * 2 ^ 59
def prefixEnd_1901272 : Nat := 4983230072969 + 3 ^ 40 * 1901272 * 2
def baseEnd_1901272 : Nat := 36158014479081129565045

theorem tailTrace_1901272 : CollatzResearch.WordTrace tailWord_1901272 prefixEnd_1901272 36158014479081129565045 := by
  unfold tailWord_1901272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672543384011865125557035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46230057845349153500742713 34672543384011865125557035)
  ·
    refine ⟨52008815076017797688335553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34672543384011865125557035 52008815076017797688335553)
    ·
      refine ⟨39006611307013348266251665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52008815076017797688335553 39006611307013348266251665)
      ·
        refine ⟨29254958480260011199688749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39006611307013348266251665 29254958480260011199688749)
        ·
          refine ⟨10970609430097504199883281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29254958480260011199688749 10970609430097504199883281)
          ·
            refine ⟨8227957072573128149912461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10970609430097504199883281 8227957072573128149912461)
            ·
              refine ⟨3085483902214923056217173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8227957072573128149912461 3085483902214923056217173)
              ·
                refine ⟨36158014479081129565045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3085483902214923056217173 36158014479081129565045)
                ·
                  rfl

theorem cell23_1901272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 8].length) (baseStart_1901272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901272 prefixEnd_1901272 := by exact prefixLift 1901272
  have htrace : WordTrace (prefixWord ++ tailWord_1901272) baseStart_1901272 baseEnd_1901272 := by
    simpa [prefixWord, tailWord_1901272, baseEnd_1901272] using wordTrace_append hprefix tailTrace_1901272
  have hstable : (prefixWord ++ tailWord_1901272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901272).length < 2 ^ (prefixWord ++ tailWord_1901272).sum := by decide
  have hdescent : baseEnd_1901272 < baseStart_1901272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901276 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1901276 : Nat := 118140960795 + 1901276 * 2 ^ 59
def prefixEnd_1901276 : Nat := 4983230072969 + 3 ^ 40 * 1901276 * 2
def baseEnd_1901276 : Nat := 325422814952602827535399

theorem tailTrace_1901276 : CollatzResearch.WordTrace tailWord_1901276 prefixEnd_1901276 325422814952602827535399 := by
  unfold tailWord_1901276
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672616330004619467129841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46230155106672825956173121 34672616330004619467129841)
  ·
    refine ⟨26004462247503464600347381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34672616330004619467129841 26004462247503464600347381)
    ·
      refine ⟨2437918335703449806282567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26004462247503464600347381 2437918335703449806282567)
      ·
        refine ⟨3656877503555174709423851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437918335703449806282567 3656877503555174709423851)
        ·
          refine ⟨5485316255332762064135777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656877503555174709423851 5485316255332762064135777)
          ·
            refine ⟨4113987191499571548101833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5485316255332762064135777 4113987191499571548101833)
            ·
              refine ⟨3085490393624678661076375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113987191499571548101833 3085490393624678661076375)
              ·
                refine ⟨4628235590437017991614563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085490393624678661076375 4628235590437017991614563)
                ·
                  refine ⟨6942353385655526987421845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628235590437017991614563 6942353385655526987421845)
                  ·
                    refine ⟨325422814952602827535399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6942353385655526987421845 325422814952602827535399)
                    ·
                      rfl

theorem cell23_1901276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1901276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901276 prefixEnd_1901276 := by exact prefixLift 1901276
  have htrace : WordTrace (prefixWord ++ tailWord_1901276) baseStart_1901276 baseEnd_1901276 := by
    simpa [prefixWord, tailWord_1901276, baseEnd_1901276] using wordTrace_append hprefix tailTrace_1901276
  have hstable : (prefixWord ++ tailWord_1901276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901276).length < 2 ^ (prefixWord ++ tailWord_1901276).sum := by decide
  have hdescent : baseEnd_1901276 < baseStart_1901276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901279 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1901279 : Nat := 118140960795 + 1901279 * 2 ^ 59
def prefixEnd_1901279 : Nat := 4983230072969 + 3 ^ 40 * 1901279 * 2
def baseEnd_1901279 : Nat := 976269985299771970868683

theorem tailTrace_1901279 : CollatzResearch.WordTrace tailWord_1901279 prefixEnd_1901279 976269985299771970868683 := by
  unfold tailWord_1901279
  simp only [CollatzResearch.WordTrace]
  refine ⟨69345342078998370446618891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46230228052665580297745927 69345342078998370446618891)
  ·
    refine ⟨104018013118497555669928337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69345342078998370446618891 104018013118497555669928337)
    ·
      refine ⟨78013509838873166752446253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104018013118497555669928337 78013509838873166752446253)
      ·
        refine ⟨29255066189577437532167345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78013509838873166752446253 29255066189577437532167345)
        ·
          refine ⟨21941299642183078149125509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29255066189577437532167345 21941299642183078149125509)
          ·
            refine ⟨4113993682909327152961033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21941299642183078149125509 4113993682909327152961033)
            ·
              refine ⟨3085495262181995364720775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113993682909327152961033 3085495262181995364720775)
              ·
                refine ⟨4628242893272993047081163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085495262181995364720775 4628242893272993047081163)
                ·
                  refine ⟨6942364339909489570621745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628242893272993047081163 6942364339909489570621745)
                  ·
                    refine ⟨5206773254932117177966309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942364339909489570621745 5206773254932117177966309)
                    ·
                      refine ⟨976269985299771970868683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5206773254932117177966309 976269985299771970868683)
                      ·
                        rfl

theorem cell23_1901279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1901279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901279 prefixEnd_1901279 := by exact prefixLift 1901279
  have htrace : WordTrace (prefixWord ++ tailWord_1901279) baseStart_1901279 baseEnd_1901279 := by
    simpa [prefixWord, tailWord_1901279, baseEnd_1901279] using wordTrace_append hprefix tailTrace_1901279
  have hstable : (prefixWord ++ tailWord_1901279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901279).length < 2 ^ (prefixWord ++ tailWord_1901279).sum := by decide
  have hdescent : baseEnd_1901279 < baseStart_1901279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901283 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1901283 : Nat := 118140960795 + 1901283 * 2 ^ 59
def prefixEnd_1901283 : Nat := 4983230072969 + 3 ^ 40 * 1901283 * 2
def baseEnd_1901283 : Nat := 976272039222389955218665

theorem tailTrace_1901283 : CollatzResearch.WordTrace tailWord_1901283 prefixEnd_1901283 976272039222389955218665 := by
  unfold tailWord_1901283
  simp only [CollatzResearch.WordTrace]
  refine ⟨69345487970983879129764503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46230325313989252753176335 69345487970983879129764503)
  ·
    refine ⟨104018231956475818694646755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69345487970983879129764503 104018231956475818694646755)
    ·
      refine ⟨156027347934713728041970133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104018231956475818694646755 156027347934713728041970133)
      ·
        refine ⟨3656890967219853000983675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 156027347934713728041970133 3656890967219853000983675)
        ·
          refine ⟨5485336450829779501475513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656890967219853000983675 5485336450829779501475513)
          ·
            refine ⟨4114002338122334626106635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5485336450829779501475513 4114002338122334626106635)
            ·
              refine ⟨6171003507183501939159953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114002338122334626106635 6171003507183501939159953)
              ·
                refine ⟨4628252630387626454369965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171003507183501939159953 4628252630387626454369965)
                ·
                  refine ⟨1735594736395359920388737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4628252630387626454369965 1735594736395359920388737)
                  ·
                    refine ⟨1301696052296519940291553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735594736395359920388737 1301696052296519940291553)
                    ·
                      refine ⟨976272039222389955218665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301696052296519940291553 976272039222389955218665)
                      ·
                        rfl

theorem cell23_1901283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1901283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901283 prefixEnd_1901283 := by exact prefixLift 1901283
  have htrace : WordTrace (prefixWord ++ tailWord_1901283) baseStart_1901283 baseEnd_1901283 := by
    simpa [prefixWord, tailWord_1901283, baseEnd_1901283] using wordTrace_append hprefix tailTrace_1901283
  have hstable : (prefixWord ++ tailWord_1901283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901283).length < 2 ^ (prefixWord ++ tailWord_1901283).sum := by decide
  have hdescent : baseEnd_1901283 < baseStart_1901283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901299 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 3]
def baseStart_1901299 : Nat := 118140960795 + 1901299 * 2 ^ 59
def prefixEnd_1901299 : Nat := 4983230072969 + 3 ^ 40 * 1901299 * 2
def baseEnd_1901299 : Nat := 976280254912861892618591

theorem tailTrace_1901299 : CollatzResearch.WordTrace tailWord_1901299 prefixEnd_1901299 976280254912861892618591 := by
  unfold tailWord_1901299
  simp only [CollatzResearch.WordTrace]
  refine ⟨69346071538925913862346951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46230714359283942574897967 69346071538925913862346951)
  ·
    refine ⟨104019107308388870793520427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69346071538925913862346951 104019107308388870793520427)
    ·
      refine ⟨156028660962583306190280641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104019107308388870793520427 156028660962583306190280641)
      ·
        refine ⟨117021495721937479642710481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156028660962583306190280641 117021495721937479642710481)
        ·
          refine ⟨87766121791453109732032861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117021495721937479642710481 87766121791453109732032861)
          ·
            refine ⟨32912295671794916149512323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87766121791453109732032861 32912295671794916149512323)
            ·
              refine ⟨49368443507692374224268485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32912295671794916149512323 49368443507692374224268485)
              ·
                refine ⟨9256583157692320167050341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49368443507692374224268485 9256583157692320167050341)
                ·
                  refine ⟨1735609342067310031321939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9256583157692320167050341 1735609342067310031321939)
                  ·
                    refine ⟨2603414013100965046982909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735609342067310031321939 2603414013100965046982909)
                    ·
                      refine ⟨976280254912861892618591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603414013100965046982909 976280254912861892618591)
                      ·
                        rfl

theorem cell23_1901299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 3].length) (baseStart_1901299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901299 prefixEnd_1901299 := by exact prefixLift 1901299
  have htrace : WordTrace (prefixWord ++ tailWord_1901299) baseStart_1901299 baseEnd_1901299 := by
    simpa [prefixWord, tailWord_1901299, baseEnd_1901299] using wordTrace_append hprefix tailTrace_1901299
  have hstable : (prefixWord ++ tailWord_1901299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901299).length < 2 ^ (prefixWord ++ tailWord_1901299).sum := by decide
  have hdescent : baseEnd_1901299 < baseStart_1901299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901300 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1901300 : Nat := 118140960795 + 1901300 * 2 ^ 59
def prefixEnd_1901300 : Nat := 4983230072969 + 3 ^ 40 * 1901300 * 2
def baseEnd_1901300 : Nat := 976280768393516388706087

theorem tailTrace_1901300 : CollatzResearch.WordTrace tailWord_1901300 prefixEnd_1901300 976280768393516388706087 := by
  unfold tailWord_1901300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673054005961145516566677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46230738674614860688755569 34673054005961145516566677)
  ·
    refine ⟨1625299406529428696089063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34673054005961145516566677 1625299406529428696089063)
    ·
      refine ⟨2437949109794143044133595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625299406529428696089063 2437949109794143044133595)
      ·
        refine ⟨3656923664691214566200393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437949109794143044133595 3656923664691214566200393)
        ·
          refine ⟨2742692748518410924650295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656923664691214566200393 2742692748518410924650295)
          ·
            refine ⟨4114039122777616386975443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742692748518410924650295 4114039122777616386975443)
            ·
              refine ⟨6171058684166424580463165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114039122777616386975443 6171058684166424580463165)
              ·
                refine ⟨2314147006562409217673687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6171058684166424580463165 2314147006562409217673687)
                ·
                  refine ⟨3471220509843613826510531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314147006562409217673687 3471220509843613826510531)
                  ·
                    refine ⟨5206830764765420739765797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3471220509843613826510531 5206830764765420739765797)
                    ·
                      refine ⟨976280768393516388706087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5206830764765420739765797 976280768393516388706087)
                      ·
                        rfl

theorem cell23_1901300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1901300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901300 prefixEnd_1901300 := by exact prefixLift 1901300
  have htrace : WordTrace (prefixWord ++ tailWord_1901300) baseStart_1901300 baseEnd_1901300 := by
    simpa [prefixWord, tailWord_1901300, baseEnd_1901300] using wordTrace_append hprefix tailTrace_1901300
  have hstable : (prefixWord ++ tailWord_1901300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901300).length < 2 ^ (prefixWord ++ tailWord_1901300).sum := by decide
  have hdescent : baseEnd_1901300 < baseStart_1901300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901316 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1901316 : Nat := 118140960795 + 1901316 * 2 ^ 59
def prefixEnd_1901316 : Nat := 4983230072969 + 3 ^ 40 * 1901316 * 2
def baseEnd_1901316 : Nat := 976288984083988326106013

theorem tailTrace_1901316 : CollatzResearch.WordTrace tailWord_1901316 prefixEnd_1901316 976288984083988326106013 := by
  unfold tailWord_1901316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673345789932162882857901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46231127719909550510477201 34673345789932162882857901)
  ·
    refine ⟨13002504671224561081071713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34673345789932162882857901 13002504671224561081071713)
    ·
      refine ⟨9751878503418420810803785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13002504671224561081071713 9751878503418420810803785)
      ·
        refine ⟨7313908877563815608102839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9751878503418420810803785 7313908877563815608102839)
        ·
          refine ⟨10970863316345723412154259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313908877563815608102839 10970863316345723412154259)
          ·
            refine ⟨16456294974518585118231389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970863316345723412154259 16456294974518585118231389)
            ·
              refine ⟨6171110615444469419336771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16456294974518585118231389 6171110615444469419336771)
              ·
                refine ⟨9256665923166704129005157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171110615444469419336771 9256665923166704129005157)
                ·
                  refine ⟨1735624860593757024188467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9256665923166704129005157 1735624860593757024188467)
                  ·
                    refine ⟨2603437290890635536282701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735624860593757024188467 2603437290890635536282701)
                    ·
                      refine ⟨976288984083988326106013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603437290890635536282701 976288984083988326106013)
                      ·
                        rfl

theorem cell23_1901316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1901316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901316 prefixEnd_1901316 := by exact prefixLift 1901316
  have htrace : WordTrace (prefixWord ++ tailWord_1901316) baseStart_1901316 baseEnd_1901316 := by
    simpa [prefixWord, tailWord_1901316, baseEnd_1901316] using wordTrace_append hprefix tailTrace_1901316
  have hstable : (prefixWord ++ tailWord_1901316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901316).length < 2 ^ (prefixWord ++ tailWord_1901316).sum := by decide
  have hdescent : baseEnd_1901316 < baseStart_1901316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901330 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1901330 : Nat := 118140960795 + 1901330 * 2 ^ 59
def prefixEnd_1901330 : Nat := 4983230072969 + 3 ^ 40 * 1901330 * 2
def baseEnd_1901330 : Nat := 976296172813151271330949

theorem tailTrace_1901330 : CollatzResearch.WordTrace tailWord_1901330 prefixEnd_1901330 976296172813151271330949 := by
  unfold tailWord_1901330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336800550453401539181361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46231468134542404104483629 17336800550453401539181361)
  ·
    refine ⟨13002600412840051154386021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17336800550453401539181361 13002600412840051154386021)
    ·
      refine ⟨2437987577407509591447379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13002600412840051154386021 2437987577407509591447379)
      ·
        refine ⟨3656981366111264387171069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437987577407509591447379 3656981366111264387171069)
        ·
          refine ⟨1371368012291724145189151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3656981366111264387171069 1371368012291724145189151)
          ·
            refine ⟨2057052018437586217783727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371368012291724145189151 2057052018437586217783727)
            ·
              refine ⟨3085578027656379326675591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057052018437586217783727 3085578027656379326675591)
              ·
                refine ⟨4628367041484568990013387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085578027656379326675591 4628367041484568990013387)
                ·
                  refine ⟨6942550562226853485020081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628367041484568990013387 6942550562226853485020081)
                  ·
                    refine ⟨5206912921670140113765061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942550562226853485020081 5206912921670140113765061)
                    ·
                      refine ⟨976296172813151271330949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5206912921670140113765061 976296172813151271330949)
                      ·
                        rfl

theorem cell23_1901330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1901330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901330 prefixEnd_1901330 := by exact prefixLift 1901330
  have htrace : WordTrace (prefixWord ++ tailWord_1901330) baseStart_1901330 baseEnd_1901330 := by
    simpa [prefixWord, tailWord_1901330, baseEnd_1901330] using wordTrace_append hprefix tailTrace_1901330
  have hstable : (prefixWord ++ tailWord_1901330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901330).length < 2 ^ (prefixWord ++ tailWord_1901330).sum := by decide
  have hdescent : baseEnd_1901330 < baseStart_1901330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901333 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_1901333 : Nat := 118140960795 + 1901333 * 2 ^ 59
def prefixEnd_1901333 : Nat := 4983230072969 + 3 ^ 40 * 1901333 * 2
def baseEnd_1901333 : Nat := 976297713255114759593435

theorem tailTrace_1901333 : CollatzResearch.WordTrace tailWord_1901333 prefixEnd_1901333 976297713255114759593435 := by
  unfold tailWord_1901333
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347311620802737669084653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46231541080535158446056435 69347311620802737669084653)
  ·
    refine ⟨26005241857801026625906745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69347311620802737669084653 26005241857801026625906745)
    ·
      refine ⟨19503931393350769969430059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26005241857801026625906745 19503931393350769969430059)
      ·
        refine ⟨29255897090026154954145089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503931393350769969430059 29255897090026154954145089)
        ·
          refine ⟨21941922817519616215608817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29255897090026154954145089 21941922817519616215608817)
          ·
            refine ⟨16456442113139712161706613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21941922817519616215608817 16456442113139712161706613)
            ·
              refine ⟨1542791448106848015159995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16456442113139712161706613 1542791448106848015159995)
              ·
                refine ⟨2314187172160272022739993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542791448106848015159995 2314187172160272022739993)
                ·
                  refine ⟨1735640379120204017054995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314187172160272022739993 1735640379120204017054995)
                  ·
                    refine ⟨2603460568680306025582493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735640379120204017054995 2603460568680306025582493)
                    ·
                      refine ⟨976297713255114759593435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603460568680306025582493 976297713255114759593435)
                      ·
                        rfl

theorem cell23_1901333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_1901333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901333 prefixEnd_1901333 := by exact prefixLift 1901333
  have htrace : WordTrace (prefixWord ++ tailWord_1901333) baseStart_1901333 baseEnd_1901333 := by
    simpa [prefixWord, tailWord_1901333, baseEnd_1901333] using wordTrace_append hprefix tailTrace_1901333
  have hstable : (prefixWord ++ tailWord_1901333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901333).length < 2 ^ (prefixWord ++ tailWord_1901333).sum := by decide
  have hdescent : baseEnd_1901333 < baseStart_1901333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901343 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 1, 3, 2]
def baseStart_1901343 : Nat := 118140960795 + 1901343 * 2 ^ 59
def prefixEnd_1901343 : Nat := 4983230072969 + 3 ^ 40 * 1901343 * 2
def baseEnd_1901343 : Nat := 976302848061659720468389

theorem tailTrace_1901343 : CollatzResearch.WordTrace tailWord_1901343 prefixEnd_1901343 976302848061659720468389 := by
  unfold tailWord_1901343
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347676350766509376948683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46231784233844339584632455 69347676350766509376948683)
  ·
    refine ⟨104021514526149764065423025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69347676350766509376948683 104021514526149764065423025)
    ·
      refine ⟨78016135894612323049067269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104021514526149764065423025 78016135894612323049067269)
      ·
        refine ⟨14628025480239810571700113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78016135894612323049067269 14628025480239810571700113)
        ·
          refine ⟨10971019110179857928775085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14628025480239810571700113 10971019110179857928775085)
          ·
            refine ⟨4114132166317446723290657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10971019110179857928775085 4114132166317446723290657)
            ·
              refine ⟨3085599124738085042467993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4114132166317446723290657 3085599124738085042467993)
              ·
                refine ⟨2314199343553563781850995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085599124738085042467993 2314199343553563781850995)
                ·
                  refine ⟨3471299015330345672776493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314199343553563781850995 3471299015330345672776493)
                  ·
                    refine ⟨1301737130748879627291185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3471299015330345672776493 1301737130748879627291185)
                    ·
                      refine ⟨976302848061659720468389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301737130748879627291185 976302848061659720468389)
                      ·
                        rfl

theorem cell23_1901343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_1901343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901343 prefixEnd_1901343 := by exact prefixLift 1901343
  have htrace : WordTrace (prefixWord ++ tailWord_1901343) baseStart_1901343 baseEnd_1901343 := by
    simpa [prefixWord, tailWord_1901343, baseEnd_1901343] using wordTrace_append hprefix tailTrace_1901343
  have hstable : (prefixWord ++ tailWord_1901343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901343).length < 2 ^ (prefixWord ++ tailWord_1901343).sum := by decide
  have hdescent : baseEnd_1901343 < baseStart_1901343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901356 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_1901356 : Nat := 118140960795 + 1901356 * 2 ^ 59
def prefixEnd_1901356 : Nat := 4983230072969 + 3 ^ 40 * 1901356 * 2
def baseEnd_1901356 : Nat := 976309523310168169605829

theorem tailTrace_1901356 : CollatzResearch.WordTrace tailWord_1901356 prefixEnd_1901356 976309523310168169605829 := by
  unfold tailWord_1901356
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674075249859706298585961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46232100333146275064781281 34674075249859706298585961)
  ·
    refine ⟨26005556437394779723939471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34674075249859706298585961 26005556437394779723939471)
    ·
      refine ⟨39008334656092169585909207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26005556437394779723939471 39008334656092169585909207)
      ·
        refine ⟨58512501984138254378863811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39008334656092169585909207 58512501984138254378863811)
        ·
          refine ⟨87768752976207381568295717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58512501984138254378863811 87768752976207381568295717)
          ·
            refine ⟨16456641183038884044055447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87768752976207381568295717 16456641183038884044055447)
            ·
              refine ⟨24684961774558326066083171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16456641183038884044055447 24684961774558326066083171)
              ·
                refine ⟨37027442661837489099124757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24684961774558326066083171 37027442661837489099124757)
                ·
                  refine ⟨1735661374773632301521473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37027442661837489099124757 1735661374773632301521473)
                  ·
                    refine ⟨1301746031080224226141105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735661374773632301521473 1301746031080224226141105)
                    ·
                      refine ⟨976309523310168169605829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301746031080224226141105 976309523310168169605829)
                      ·
                        rfl

theorem cell23_1901356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_1901356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901356 prefixEnd_1901356 := by exact prefixLift 1901356
  have htrace : WordTrace (prefixWord ++ tailWord_1901356) baseStart_1901356 baseEnd_1901356 := by
    simpa [prefixWord, tailWord_1901356, baseEnd_1901356] using wordTrace_append hprefix tailTrace_1901356
  have hstable : (prefixWord ++ tailWord_1901356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901356).length < 2 ^ (prefixWord ++ tailWord_1901356).sum := by decide
  have hdescent : baseEnd_1901356 < baseStart_1901356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901372 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1901372 : Nat := 118140960795 + 1901372 * 2 ^ 59
def prefixEnd_1901372 : Nat := 4983230072969 + 3 ^ 40 * 1901372 * 2
def baseEnd_1901372 : Nat := 976317739000640107005755

theorem tailTrace_1901372 : CollatzResearch.WordTrace tailWord_1901372 prefixEnd_1901372 976317739000640107005755 := by
  unfold tailWord_1901372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674367033830723664877185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46232489378440964886502913 34674367033830723664877185)
  ·
    refine ⟨26005775275373042748657889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34674367033830723664877185 26005775275373042748657889)
    ·
      refine ⟨19504331456529782061493417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26005775275373042748657889 19504331456529782061493417)
      ·
        refine ⟨14628248592397336546120063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19504331456529782061493417 14628248592397336546120063)
        ·
          refine ⟨21942372888596004819180095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14628248592397336546120063 21942372888596004819180095)
          ·
            refine ⟨32913559332894007228770143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21942372888596004819180095 32913559332894007228770143)
            ·
              refine ⟨49370338999341010843155215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32913559332894007228770143 49370338999341010843155215)
              ·
                refine ⟨74055508499011516264732823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49370338999341010843155215 74055508499011516264732823)
                ·
                  refine ⟨111083262748517274397099235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74055508499011516264732823 111083262748517274397099235)
                  ·
                    refine ⟨166624894122775911595648853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111083262748517274397099235 166624894122775911595648853)
                    ·
                      refine ⟨976317739000640107005755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 166624894122775911595648853 976317739000640107005755)
                      ·
                        rfl

theorem cell23_1901372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1901372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901372 prefixEnd_1901372 := by exact prefixLift 1901372
  have htrace : WordTrace (prefixWord ++ tailWord_1901372) baseStart_1901372 baseEnd_1901372 := by
    simpa [prefixWord, tailWord_1901372, baseEnd_1901372] using wordTrace_append hprefix tailTrace_1901372
  have hstable : (prefixWord ++ tailWord_1901372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901372).length < 2 ^ (prefixWord ++ tailWord_1901372).sum := by decide
  have hdescent : baseEnd_1901372 < baseStart_1901372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901392 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_1901392 : Nat := 118140960795 + 1901392 * 2 ^ 59
def prefixEnd_1901392 : Nat := 4983230072969 + 3 ^ 40 * 1901392 * 2
def baseEnd_1901392 : Nat := 325442669537910009585221

theorem tailTrace_1901392 : CollatzResearch.WordTrace tailWord_1901392 prefixEnd_1901392 325442669537910009585221 := by
  unfold tailWord_1901392
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674731763794495372741215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46232975685059327163654953 34674731763794495372741215)
  ·
    refine ⟨52012097645691743059111823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34674731763794495372741215 52012097645691743059111823)
    ·
      refine ⟨78018146468537614588667735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52012097645691743059111823 78018146468537614588667735)
      ·
        refine ⟨117027219702806421883001603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78018146468537614588667735 117027219702806421883001603)
        ·
          refine ⟨175540829554209632824502405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117027219702806421883001603 175540829554209632824502405)
          ·
            refine ⟨32913905541414306154594201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175540829554209632824502405 32913905541414306154594201)
            ·
              refine ⟨24685429156060729615945651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32913905541414306154594201 24685429156060729615945651)
              ·
                refine ⟨37028143734091094423918477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24685429156060729615945651 37028143734091094423918477)
                ·
                  refine ⟨13885553900284160408969429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37028143734091094423918477 13885553900284160408969429)
                  ·
                    refine ⟨325442669537910009585221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13885553900284160408969429 325442669537910009585221)
                    ·
                      rfl

theorem cell23_1901392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_1901392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901392 prefixEnd_1901392 := by exact prefixLift 1901392
  have htrace : WordTrace (prefixWord ++ tailWord_1901392) baseStart_1901392 baseEnd_1901392 := by
    simpa [prefixWord, tailWord_1901392, baseEnd_1901392] using wordTrace_append hprefix tailTrace_1901392
  have hstable : (prefixWord ++ tailWord_1901392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901392).length < 2 ^ (prefixWord ++ tailWord_1901392).sum := by decide
  have hdescent : baseEnd_1901392 < baseStart_1901392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901430 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1901430 : Nat := 118140960795 + 1901430 * 2 ^ 59
def prefixEnd_1901430 : Nat := 4983230072969 + 3 ^ 40 * 1901430 * 2
def baseEnd_1901430 : Nat := 108483057875400097786721

theorem tailTrace_1901430 : CollatzResearch.WordTrace tailWord_1901430 prefixEnd_1901430 108483057875400097786721 := by
  unfold tailWord_1901430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334428093840707702210359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46233899667634215490243829 4334428093840707702210359)
  ·
    refine ⟨6501642140761061553315539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4334428093840707702210359 6501642140761061553315539)
    ·
      refine ⟨9752463211141592329973309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501642140761061553315539 9752463211141592329973309)
      ·
        refine ⟨3657173704178097123739991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9752463211141592329973309 3657173704178097123739991)
        ·
          refine ⟨5485760556267145685609987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657173704178097123739991 5485760556267145685609987)
          ·
            refine ⟨8228640834400718528414981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485760556267145685609987 8228640834400718528414981)
            ·
              refine ⟨1542870156450134724077809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8228640834400718528414981 1542870156450134724077809)
              ·
                refine ⟨1157152617337601043058357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542870156450134724077809 1157152617337601043058357)
                ·
                  refine ⟨108483057875400097786721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157152617337601043058357 108483057875400097786721)
                  ·
                    rfl

theorem cell23_1901430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1901430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901430 prefixEnd_1901430 := by exact prefixLift 1901430
  have htrace : WordTrace (prefixWord ++ tailWord_1901430) baseStart_1901430 baseEnd_1901430 := by
    simpa [prefixWord, tailWord_1901430, baseEnd_1901430] using wordTrace_append hprefix tailTrace_1901430
  have hstable : (prefixWord ++ tailWord_1901430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901430).length < 2 ^ (prefixWord ++ tailWord_1901430).sum := by decide
  have hdescent : baseEnd_1901430 < baseStart_1901430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901469 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 8]
def baseStart_1901469 : Nat := 118140960795 + 1901469 * 2 ^ 59
def prefixEnd_1901469 : Nat := 4983230072969 + 3 ^ 40 * 1901469 * 2
def baseEnd_1901469 : Nat := 108485282958236247499201

theorem tailTrace_1901469 : CollatzResearch.WordTrace tailWord_1901469 prefixEnd_1901469 108485282958236247499201 := by
  unfold tailWord_1901469
  simp only [CollatzResearch.WordTrace]
  refine ⟨69352271948310032896035461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46234847965540021930690307 69352271948310032896035461)
  ·
    refine ⟨13003550990308131168006649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69352271948310032896035461 13003550990308131168006649)
    ·
      refine ⟨9752663242731098376004987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13003550990308131168006649 9752663242731098376004987)
      ·
        refine ⟨14628994864096647564007481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9752663242731098376004987 14628994864096647564007481)
        ·
          refine ⟨10971746148072485673005611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14628994864096647564007481 10971746148072485673005611)
          ·
            refine ⟨16457619222108728509508417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971746148072485673005611 16457619222108728509508417)
            ·
              refine ⟨12343214416581546382131313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16457619222108728509508417 12343214416581546382131313)
              ·
                refine ⟨9257410812436159786598485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12343214416581546382131313 9257410812436159786598485)
                ·
                  refine ⟨108485282958236247499201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9257410812436159786598485 108485282958236247499201)
                  ·
                    rfl

theorem cell23_1901469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_1901469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901469 prefixEnd_1901469 := by exact prefixLift 1901469
  have htrace : WordTrace (prefixWord ++ tailWord_1901469) baseStart_1901469 baseEnd_1901469 := by
    simpa [prefixWord, tailWord_1901469, baseEnd_1901469] using wordTrace_append hprefix tailTrace_1901469
  have hstable : (prefixWord ++ tailWord_1901469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901469).length < 2 ^ (prefixWord ++ tailWord_1901469).sum := by decide
  have hdescent : baseEnd_1901469 < baseStart_1901469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901533 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1901533 : Nat := 118140960795 + 1901533 * 2 ^ 59
def prefixEnd_1901533 : Nat := 4983230072969 + 3 ^ 40 * 1901533 * 2
def baseEnd_1901533 : Nat := 325466803128671325697505

theorem tailTrace_1901533 : CollatzResearch.WordTrace tailWord_1901533 prefixEnd_1901533 325466803128671325697505 := by
  unfold tailWord_1901533
  simp only [CollatzResearch.WordTrace]
  refine ⟨69354606220078171826365253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46236404146718781217576835 69354606220078171826365253)
  ·
    refine ⟨13003988666264657217443485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69354606220078171826365253 13003988666264657217443485)
    ·
      refine ⟨4876495749849246456541307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13003988666264657217443485 4876495749849246456541307)
      ·
        refine ⟨7314743624773869684811961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876495749849246456541307 7314743624773869684811961)
        ·
          refine ⟨5486057718580402263608971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7314743624773869684811961 5486057718580402263608971)
          ·
            refine ⟨8229086577870603395413457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486057718580402263608971 8229086577870603395413457)
            ·
              refine ⟨6171814933402952546560093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8229086577870603395413457 6171814933402952546560093)
              ·
                refine ⟨2314430600026107204960035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6171814933402952546560093 2314430600026107204960035)
                ·
                  refine ⟨3471645900039160807440053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314430600026107204960035 3471645900039160807440053)
                  ·
                    refine ⟨325466803128671325697505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3471645900039160807440053 325466803128671325697505)
                    ·
                      rfl

theorem cell23_1901533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1901533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901533 prefixEnd_1901533 := by exact prefixLift 1901533
  have htrace : WordTrace (prefixWord ++ tailWord_1901533) baseStart_1901533 baseEnd_1901533 := by
    simpa [prefixWord, tailWord_1901533, baseEnd_1901533] using wordTrace_append hprefix tailTrace_1901533
  have hstable : (prefixWord ++ tailWord_1901533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901533).length < 2 ^ (prefixWord ++ tailWord_1901533).sum := by decide
  have hdescent : baseEnd_1901533 < baseStart_1901533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901604 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1901604 : Nat := 118140960795 + 1901604 * 2 ^ 59
def prefixEnd_1901604 : Nat := 4983230072969 + 3 ^ 40 * 1901604 * 2
def baseEnd_1901604 : Nat := 976436866512483199304689

theorem tailTrace_1901604 : CollatzResearch.WordTrace tailWord_1901604 prefixEnd_1901604 976436866512483199304689 := by
  unfold tailWord_1901604
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678597901410475476099933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46238130535213967301466577 34678597901410475476099933)
  ·
    refine ⟨13004474213028928303537475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34678597901410475476099933 13004474213028928303537475)
    ·
      refine ⟨19506711319543392455306213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004474213028928303537475 19506711319543392455306213)
      ·
        refine ⟨3657508372414386085369915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19506711319543392455306213 3657508372414386085369915)
        ·
          refine ⟨5486262558621579128054873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657508372414386085369915 5486262558621579128054873)
          ·
            refine ⟨4114696918966184346041155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5486262558621579128054873 4114696918966184346041155)
            ·
              refine ⟨6172045378449276519061733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114696918966184346041155 6172045378449276519061733)
              ·
                refine ⟨1157258508459239347324075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6172045378449276519061733 1157258508459239347324075)
                ·
                  refine ⟨1735887762688859020986113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157258508459239347324075 1735887762688859020986113)
                  ·
                    refine ⟨1301915822016644265739585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1735887762688859020986113 1301915822016644265739585)
                    ·
                      refine ⟨976436866512483199304689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301915822016644265739585 976436866512483199304689)
                      ·
                        rfl

theorem cell23_1901604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1901604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901604 prefixEnd_1901604 := by exact prefixLift 1901604
  have htrace : WordTrace (prefixWord ++ tailWord_1901604) baseStart_1901604 baseEnd_1901604 := by
    simpa [prefixWord, tailWord_1901604, baseEnd_1901604] using wordTrace_append hprefix tailTrace_1901604
  have hstable : (prefixWord ++ tailWord_1901604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901604).length < 2 ^ (prefixWord ++ tailWord_1901604).sum := by decide
  have hdescent : baseEnd_1901604 < baseStart_1901604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901610 : List Nat := [3, 1, 4, 1, 4, 1, 1, 8]
def baseStart_1901610 : Nat := 118140960795 + 1901610 * 2 ^ 59
def prefixEnd_1901610 : Nat := 4983230072969 + 3 ^ 40 * 1901610 * 2
def baseEnd_1901610 : Nat := 36164442496163339845543

theorem tailTrace_1901610 : CollatzResearch.WordTrace tailWord_1901610 prefixEnd_1901610 36164442496163339845543 := by
  unfold tailWord_1901610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17339353660199803494229571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46238276427199475984612189 17339353660199803494229571)
  ·
    refine ⟨26009030490299705241344357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17339353660199803494229571 26009030490299705241344357)
    ·
      refine ⟨4876693216931194732752067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26009030490299705241344357 4876693216931194732752067)
      ·
        refine ⟨7315039825396792099128101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876693216931194732752067 7315039825396792099128101)
        ·
          refine ⟨1371569967261898518586519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7315039825396792099128101 1371569967261898518586519)
          ·
            refine ⟨2057354950892847777879779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371569967261898518586519 2057354950892847777879779)
            ·
              refine ⟨3086032426339271666819669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057354950892847777879779 3086032426339271666819669)
              ·
                refine ⟨36164442496163339845543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3086032426339271666819669 36164442496163339845543)
                ·
                  rfl

theorem cell23_1901610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_1901610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901610 prefixEnd_1901610 := by exact prefixLift 1901610
  have htrace : WordTrace (prefixWord ++ tailWord_1901610) baseStart_1901610 baseEnd_1901610 := by
    simpa [prefixWord, tailWord_1901610, baseEnd_1901610] using wordTrace_append hprefix tailTrace_1901610
  have hstable : (prefixWord ++ tailWord_1901610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901610).length < 2 ^ (prefixWord ++ tailWord_1901610).sum := by decide
  have hdescent : baseEnd_1901610 < baseStart_1901610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901620 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1901620 : Nat := 118140960795 + 1901620 * 2 ^ 59
def prefixEnd_1901620 : Nat := 4983230072969 + 3 ^ 40 * 1901620 * 2
def baseEnd_1901620 : Nat := 976445082202955136704615

theorem tailTrace_1901620 : CollatzResearch.WordTrace tailWord_1901620 prefixEnd_1901620 976445082202955136704615 := by
  unfold tailWord_1901620
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678889685381492842391157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46238519580508657123188209 34678889685381492842391157)
  ·
    refine ⟨3251145908004514953974171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34678889685381492842391157 3251145908004514953974171)
    ·
      refine ⟨4876718862006772430961257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3251145908004514953974171 4876718862006772430961257)
      ·
        refine ⟨3657539146505079323220943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4876718862006772430961257 3657539146505079323220943)
        ·
          refine ⟨5486308719757618984831415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3657539146505079323220943 5486308719757618984831415)
          ·
            refine ⟨8229463079636428477247123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486308719757618984831415 8229463079636428477247123)
            ·
              refine ⟨12344194619454642715870685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229463079636428477247123 12344194619454642715870685)
              ·
                refine ⟨4629072982295491018451507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12344194619454642715870685 4629072982295491018451507)
                ·
                  refine ⟨6943609473443236527677261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629072982295491018451507 6943609473443236527677261)
                  ·
                    refine ⟨2603853552541213697878973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6943609473443236527677261 2603853552541213697878973)
                    ·
                      refine ⟨976445082202955136704615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603853552541213697878973 976445082202955136704615)
                      ·
                        rfl

theorem cell23_1901620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1901620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901620 prefixEnd_1901620 := by exact prefixLift 1901620
  have htrace : WordTrace (prefixWord ++ tailWord_1901620) baseStart_1901620 baseEnd_1901620 := by
    simpa [prefixWord, tailWord_1901620, baseEnd_1901620] using wordTrace_append hprefix tailTrace_1901620
  have hstable : (prefixWord ++ tailWord_1901620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901620).length < 2 ^ (prefixWord ++ tailWord_1901620).sum := by decide
  have hdescent : baseEnd_1901620 < baseStart_1901620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901646 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1901646 : Nat := 118140960795 + 1901646 * 2 ^ 59
def prefixEnd_1901646 : Nat := 4983230072969 + 3 ^ 40 * 1901646 * 2
def baseEnd_1901646 : Nat := 976458432699972034979495

theorem tailTrace_1901646 : CollatzResearch.WordTrace tailWord_1901646 prefixEnd_1901646 976458432699972034979495 := by
  unfold tailWord_1901646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669840958583599015653599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46239151779112528083485861 8669840958583599015653599)
  ·
    refine ⟨13004761437875398523480399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669840958583599015653599 13004761437875398523480399)
    ·
      refine ⟨19507142156813097785220599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13004761437875398523480399 19507142156813097785220599)
      ·
        refine ⟨29260713235219646677830899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19507142156813097785220599 29260713235219646677830899)
        ·
          refine ⟨43891069852829470016746349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29260713235219646677830899 43891069852829470016746349)
          ·
            refine ⟨16459151194811051256279881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43891069852829470016746349 16459151194811051256279881)
            ·
              refine ⟨12344363396108288442209911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16459151194811051256279881 12344363396108288442209911)
              ·
                refine ⟨18516545094162432663314867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344363396108288442209911 18516545094162432663314867)
                ·
                  refine ⟨27774817641243648994972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18516545094162432663314867 27774817641243648994972301)
                  ·
                    refine ⟨10415556615466368373114613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27774817641243648994972301 10415556615466368373114613)
                    ·
                      refine ⟨976458432699972034979495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10415556615466368373114613 976458432699972034979495)
                      ·
                        rfl

theorem cell23_1901646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1901646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901646 prefixEnd_1901646 := by exact prefixLift 1901646
  have htrace : WordTrace (prefixWord ++ tailWord_1901646) baseStart_1901646 baseEnd_1901646 := by
    simpa [prefixWord, tailWord_1901646, baseEnd_1901646] using wordTrace_append hprefix tailTrace_1901646
  have hstable : (prefixWord ++ tailWord_1901646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901646).length < 2 ^ (prefixWord ++ tailWord_1901646).sum := by decide
  have hdescent : baseEnd_1901646 < baseStart_1901646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901654 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1901654 : Nat := 118140960795 + 1901654 * 2 ^ 59
def prefixEnd_1901654 : Nat := 4983230072969 + 3 ^ 40 * 1901654 * 2
def baseEnd_1901654 : Nat := 976462540545208003679459

theorem tailTrace_1901654 : CollatzResearch.WordTrace tailWord_1901654 prefixEnd_1901654 976462540545208003679459 := by
  unfold tailWord_1901654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334938715789988093220001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46239346301759872994346677 4334938715789988093220001)
  ·
    refine ⟨3251204036842491069915001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4334938715789988093220001 3251204036842491069915001)
    ·
      refine ⟨2438403027631868302436251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3251204036842491069915001 2438403027631868302436251)
      ·
        refine ⟨3657604541447802453654377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438403027631868302436251 3657604541447802453654377)
        ·
          refine ⟨2743203406085851840240783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3657604541447802453654377 2743203406085851840240783)
          ·
            refine ⟨4114805109128777760361175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743203406085851840240783 4114805109128777760361175)
            ·
              refine ⟨6172207663693166640541763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4114805109128777760361175 6172207663693166640541763)
              ·
                refine ⟨9258311495539749960812645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172207663693166640541763 9258311495539749960812645)
                ·
                  refine ⟨1735933405413703117652371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9258311495539749960812645 1735933405413703117652371)
                  ·
                    refine ⟨2603900108120554676478557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735933405413703117652371 2603900108120554676478557)
                    ·
                      refine ⟨976462540545208003679459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2603900108120554676478557 976462540545208003679459)
                      ·
                        rfl

theorem cell23_1901654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1901654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901654 prefixEnd_1901654 := by exact prefixLift 1901654
  have htrace : WordTrace (prefixWord ++ tailWord_1901654) baseStart_1901654 baseEnd_1901654 := by
    simpa [prefixWord, tailWord_1901654, baseEnd_1901654] using wordTrace_append hprefix tailTrace_1901654
  have hstable : (prefixWord ++ tailWord_1901654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901654).length < 2 ^ (prefixWord ++ tailWord_1901654).sum := by decide
  have hdescent : baseEnd_1901654 < baseStart_1901654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901656 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1901656 : Nat := 118140960795 + 1901656 * 2 ^ 59
def prefixEnd_1901656 : Nat := 4983230072969 + 3 ^ 40 * 1901656 * 2
def baseEnd_1901656 : Nat := 976463567506516995854449

theorem tailTrace_1901656 : CollatzResearch.WordTrace tailWord_1901656 prefixEnd_1901656 976463567506516995854449 := by
  unfold tailWord_1901656
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679546199316281916546411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46239394932421709222061881 34679546199316281916546411)
  ·
    refine ⟨52019319298974422874819617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34679546199316281916546411 52019319298974422874819617)
    ·
      refine ⟨39014489474230817156114713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52019319298974422874819617 39014489474230817156114713)
      ·
        refine ⟨29260867105673112867086035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39014489474230817156114713 29260867105673112867086035)
        ·
          refine ⟨43891300658509669300629053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29260867105673112867086035 43891300658509669300629053)
          ·
            refine ⟨16459237746941125987735895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43891300658509669300629053 16459237746941125987735895)
            ·
              refine ⟨24688856620411688981603843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16459237746941125987735895 24688856620411688981603843)
              ·
                refine ⟨37033284930617533472405765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24688856620411688981603843 37033284930617533472405765)
                ·
                  refine ⟨6943740924490787526076081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37033284930617533472405765 6943740924490787526076081)
                  ·
                    refine ⟨5207805693368090644557061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943740924490787526076081 5207805693368090644557061)
                    ·
                      refine ⟨976463567506516995854449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5207805693368090644557061 976463567506516995854449)
                      ·
                        rfl

theorem cell23_1901656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1901656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901656 prefixEnd_1901656 := by exact prefixLift 1901656
  have htrace : WordTrace (prefixWord ++ tailWord_1901656) baseStart_1901656 baseEnd_1901656 := by
    simpa [prefixWord, tailWord_1901656, baseEnd_1901656] using wordTrace_append hprefix tailTrace_1901656
  have hstable : (prefixWord ++ tailWord_1901656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901656).length < 2 ^ (prefixWord ++ tailWord_1901656).sum := by decide
  have hdescent : baseEnd_1901656 < baseStart_1901656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901677 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_1901677 : Nat := 118140960795 + 1901677 * 2 ^ 59
def prefixEnd_1901677 : Nat := 4983230072969 + 3 ^ 40 * 1901677 * 2
def baseEnd_1901677 : Nat := 976474350600261413691853

theorem tailTrace_1901677 : CollatzResearch.WordTrace tailWord_1901677 prefixEnd_1901677 976474350600261413691853 := by
  unfold tailWord_1901677
  simp only [CollatzResearch.WordTrace]
  refine ⟨69359858331556484419607285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46239905554370989613071523 69359858331556484419607285)
  ·
    refine ⟨6502486718583420414338183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69359858331556484419607285 6502486718583420414338183)
    ·
      refine ⟨9753730077875130621507275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6502486718583420414338183 9753730077875130621507275)
      ·
        refine ⟨14630595116812695932260913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9753730077875130621507275 14630595116812695932260913)
        ·
          refine ⟨10972946337609521949195685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14630595116812695932260913 10972946337609521949195685)
          ·
            refine ⟨2057427438301785365474191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10972946337609521949195685 2057427438301785365474191)
            ·
              refine ⟨3086141157452678048211287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057427438301785365474191 3086141157452678048211287)
              ·
                refine ⟨4629211736179017072316931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086141157452678048211287 4629211736179017072316931)
                ·
                  refine ⟨6943817604268525608475397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629211736179017072316931 6943817604268525608475397)
                  ·
                    refine ⟨1301965800800348551589137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943817604268525608475397 1301965800800348551589137)
                    ·
                      refine ⟨976474350600261413691853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301965800800348551589137 976474350600261413691853)
                      ·
                        rfl

theorem cell23_1901677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_1901677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901677 prefixEnd_1901677 := by exact prefixLift 1901677
  have htrace : WordTrace (prefixWord ++ tailWord_1901677) baseStart_1901677 baseEnd_1901677 := by
    simpa [prefixWord, tailWord_1901677, baseEnd_1901677] using wordTrace_append hprefix tailTrace_1901677
  have hstable : (prefixWord ++ tailWord_1901677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901677).length < 2 ^ (prefixWord ++ tailWord_1901677).sum := by decide
  have hdescent : baseEnd_1901677 < baseStart_1901677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901696 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 7]
def baseStart_1901696 : Nat := 118140960795 + 1901696 * 2 ^ 59
def prefixEnd_1901696 : Nat := 4983230072969 + 3 ^ 40 * 1901696 * 2
def baseEnd_1901696 : Nat := 325494702244232279784755

theorem tailTrace_1901696 : CollatzResearch.WordTrace tailWord_1901696 prefixEnd_1901696 325494702244232279784755 := by
  unfold tailWord_1901696
  simp only [CollatzResearch.WordTrace]
  refine ⟨34680275659243825332274471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46240367545658433776365961 34680275659243825332274471)
  ·
    refine ⟨52020413488865737998411707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34680275659243825332274471 52020413488865737998411707)
    ·
      refine ⟨78030620233298606997617561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52020413488865737998411707 78030620233298606997617561)
      ·
        refine ⟨58522965174973955248213171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78030620233298606997617561 58522965174973955248213171)
        ·
          refine ⟨87784447762460932872319757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58522965174973955248213171 87784447762460932872319757)
          ·
            refine ⟨32919167910922849827119909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87784447762460932872319757 32919167910922849827119909)
            ·
              refine ⟨6172343983298034342584983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32919167910922849827119909 6172343983298034342584983)
              ·
                refine ⟨9258515974947051513877475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172343983298034342584983 9258515974947051513877475)
                ·
                  refine ⟨13887773962420577270816213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258515974947051513877475 13887773962420577270816213)
                  ·
                    refine ⟨325494702244232279784755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13887773962420577270816213 325494702244232279784755)
                    ·
                      rfl

theorem cell23_1901696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_1901696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901696 prefixEnd_1901696 := by exact prefixLift 1901696
  have htrace : WordTrace (prefixWord ++ tailWord_1901696) baseStart_1901696 baseEnd_1901696 := by
    simpa [prefixWord, tailWord_1901696, baseEnd_1901696] using wordTrace_append hprefix tailTrace_1901696
  have hstable : (prefixWord ++ tailWord_1901696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901696).length < 2 ^ (prefixWord ++ tailWord_1901696).sum := by decide
  have hdescent : baseEnd_1901696 < baseStart_1901696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901700 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 5]
def baseStart_1901700 : Nat := 118140960795 + 1901700 * 2 ^ 59
def prefixEnd_1901700 : Nat := 4983230072969 + 3 ^ 40 * 1901700 * 2
def baseEnd_1901700 : Nat := 108498462295034980411583

theorem tailTrace_1901700 : CollatzResearch.WordTrace tailWord_1901700 prefixEnd_1901700 108498462295034980411583 := by
  unfold tailWord_1901700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34680348605236579673847277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46240464806982106231796369 34680348605236579673847277)
  ·
    refine ⟨13005130726963717377692729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34680348605236579673847277 13005130726963717377692729)
    ·
      refine ⟨9753848045222788033269547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13005130726963717377692729 9753848045222788033269547)
      ·
        refine ⟨14630772067834182049904321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9753848045222788033269547 14630772067834182049904321)
        ·
          refine ⟨10973079050875636537428241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14630772067834182049904321 10973079050875636537428241)
          ·
            refine ⟨8229809288156727403071181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10973079050875636537428241 8229809288156727403071181)
            ·
              refine ⟨3086178483058772776151693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8229809288156727403071181 3086178483058772776151693)
              ·
                refine ⟨1157316931147039791056885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3086178483058772776151693 1157316931147039791056885)
                ·
                  refine ⟨108498462295034980411583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157316931147039791056885 108498462295034980411583)
                  ·
                    rfl

theorem cell23_1901700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_1901700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901700 prefixEnd_1901700 := by exact prefixLift 1901700
  have htrace : WordTrace (prefixWord ++ tailWord_1901700) baseStart_1901700 baseEnd_1901700 := by
    simpa [prefixWord, tailWord_1901700, baseEnd_1901700] using wordTrace_append hprefix tailTrace_1901700
  have hstable : (prefixWord ++ tailWord_1901700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901700).length < 2 ^ (prefixWord ++ tailWord_1901700).sum := by decide
  have hdescent : baseEnd_1901700 < baseStart_1901700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901703 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_1901703 : Nat := 118140960795 + 1901703 * 2 ^ 59
def prefixEnd_1901703 : Nat := 4983230072969 + 3 ^ 40 * 1901703 * 2
def baseEnd_1901703 : Nat := 976487701097278311966733

theorem tailTrace_1901703 : CollatzResearch.WordTrace tailWord_1901703 prefixEnd_1901703 976487701097278311966733 := by
  unfold tailWord_1901703
  simp only [CollatzResearch.WordTrace]
  refine ⟨69360806629462290860053763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46240537752974860573369175 69360806629462290860053763)
  ·
    refine ⟨104041209944193436290080645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69360806629462290860053763 104041209944193436290080645)
    ·
      refine ⟨19507726864536269304390121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104041209944193436290080645 19507726864536269304390121)
      ·
        refine ⟨14630795148402201978292591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19507726864536269304390121 14630795148402201978292591)
        ·
          refine ⟨21946192722603302967438887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14630795148402201978292591 21946192722603302967438887)
          ·
            refine ⟨32919289083904954451158331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21946192722603302967438887 32919289083904954451158331)
            ·
              refine ⟨49378933625857431676737497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32919289083904954451158331 49378933625857431676737497)
              ·
                refine ⟨37034200219393073757553123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49378933625857431676737497 37034200219393073757553123)
                ·
                  refine ⟨55551300329089610636329685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37034200219393073757553123 55551300329089610636329685)
                  ·
                    refine ⟨1301983601463037749288977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55551300329089610636329685 1301983601463037749288977)
                    ·
                      refine ⟨976487701097278311966733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1301983601463037749288977 976487701097278311966733)
                      ·
                        rfl

theorem cell23_1901703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_1901703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901703 prefixEnd_1901703 := by exact prefixLift 1901703
  have htrace : WordTrace (prefixWord ++ tailWord_1901703) baseStart_1901703 baseEnd_1901703 := by
    simpa [prefixWord, tailWord_1901703, baseEnd_1901703] using wordTrace_append hprefix tailTrace_1901703
  have hstable : (prefixWord ++ tailWord_1901703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901703).length < 2 ^ (prefixWord ++ tailWord_1901703).sum := by decide
  have hdescent : baseEnd_1901703 < baseStart_1901703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901743 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 3, 4]
def baseStart_1901743 : Nat := 118140960795 + 1901743 * 2 ^ 59
def prefixEnd_1901743 : Nat := 4983230072969 + 3 ^ 40 * 1901743 * 2
def baseEnd_1901743 : Nat := 325502746774486051822183

theorem tailTrace_1901743 : CollatzResearch.WordTrace tailWord_1901743 prefixEnd_1901743 325502746774486051822183 := by
  unfold tailWord_1901743
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362265549317377691509883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46241510366211585127673255 69362265549317377691509883)
  ·
    refine ⟨104043398323976066537264825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69362265549317377691509883 104043398323976066537264825)
    ·
      refine ⟨78032548742982049902948619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104043398323976066537264825 78032548742982049902948619)
      ·
        refine ⟨117048823114473074854422929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78032548742982049902948619 117048823114473074854422929)
        ·
          refine ⟨87786617335854806140817197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117048823114473074854422929 87786617335854806140817197)
          ·
            refine ⟨32919981500945552302806449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87786617335854806140817197 32919981500945552302806449)
            ·
              refine ⟨24689986125709164227104837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32919981500945552302806449 24689986125709164227104837)
              ·
                refine ⟨4629372398570468292582157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24689986125709164227104837 4629372398570468292582157)
                ·
                  refine ⟨1736014649463925609718309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4629372398570468292582157 1736014649463925609718309)
                  ·
                    refine ⟨325502746774486051822183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736014649463925609718309 325502746774486051822183)
                    ·
                      rfl

theorem cell23_1901743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_1901743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901743 prefixEnd_1901743 := by exact prefixLift 1901743
  have htrace : WordTrace (prefixWord ++ tailWord_1901743) baseStart_1901743 baseEnd_1901743 := by
    simpa [prefixWord, tailWord_1901743, baseEnd_1901743] using wordTrace_append hprefix tailTrace_1901743
  have hstable : (prefixWord ++ tailWord_1901743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901743).length < 2 ^ (prefixWord ++ tailWord_1901743).sum := by decide
  have hdescent : baseEnd_1901743 < baseStart_1901743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901770 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_1901770 : Nat := 118140960795 + 1901770 * 2 ^ 59
def prefixEnd_1901770 : Nat := 4983230072969 + 3 ^ 40 * 1901770 * 2
def baseEnd_1901770 : Nat := 976522104301129549828925

theorem tailTrace_1901770 : CollatzResearch.WordTrace tailWord_1901770 prefixEnd_1901770 976522104301129549828925 := by
  unfold tailWord_1901770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340812580054890325685691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46242166880146374201828509 17340812580054890325685691)
  ·
    refine ⟨26011218870082335488528537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17340812580054890325685691 26011218870082335488528537)
    ·
      refine ⟨19508414152561751616396403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26011218870082335488528537 19508414152561751616396403)
      ·
        refine ⟨29262621228842627424594605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508414152561751616396403 29262621228842627424594605)
        ·
          refine ⟨10973482960815985284222977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29262621228842627424594605 10973482960815985284222977)
          ·
            refine ⟨8230112220611988963167233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10973482960815985284222977 8230112220611988963167233)
            ·
              refine ⟨6172584165458991722375425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8230112220611988963167233 6172584165458991722375425)
              ·
                refine ⟨4629438124094243791781569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172584165458991722375425 4629438124094243791781569)
                ·
                  refine ⟨3472078593070682843836177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4629438124094243791781569 3472078593070682843836177)
                  ·
                    refine ⟨2604058944803012132877133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472078593070682843836177 2604058944803012132877133)
                    ·
                      refine ⟨976522104301129549828925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2604058944803012132877133 976522104301129549828925)
                      ·
                        rfl

theorem cell23_1901770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_1901770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901770 prefixEnd_1901770 := by exact prefixLift 1901770
  have htrace : WordTrace (prefixWord ++ tailWord_1901770) baseStart_1901770 baseEnd_1901770 := by
    simpa [prefixWord, tailWord_1901770, baseEnd_1901770] using wordTrace_append hprefix tailTrace_1901770
  have hstable : (prefixWord ++ tailWord_1901770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901770).length < 2 ^ (prefixWord ++ tailWord_1901770).sum := by decide
  have hdescent : baseEnd_1901770 < baseStart_1901770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901803 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 3, 5]
def baseStart_1901803 : Nat := 118140960795 + 1901803 * 2 ^ 59
def prefixEnd_1901803 : Nat := 4983230072969 + 3 ^ 40 * 1901803 * 2
def baseEnd_1901803 : Nat := 325513016387575973572091

theorem tailTrace_1901803 : CollatzResearch.WordTrace tailWord_1901803 prefixEnd_1901803 325513016387575973572091 := by
  unfold tailWord_1901803
  simp only [CollatzResearch.WordTrace]
  refine ⟨69364453929100007938694063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46242969286066671959129375 69364453929100007938694063)
  ·
    refine ⟨104046680893650011908041095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69364453929100007938694063 104046680893650011908041095)
    ·
      refine ⟨156070021340475017862061643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104046680893650011908041095 156070021340475017862061643)
      ·
        refine ⟨234105032010712526793092465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156070021340475017862061643 234105032010712526793092465)
        ·
          refine ⟨175578774008034395094819349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234105032010712526793092465 175578774008034395094819349)
          ·
            refine ⟨8230255031626612270069657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175578774008034395094819349 8230255031626612270069657)
            ·
              refine ⟨6172691273719959202552243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8230255031626612270069657 6172691273719959202552243)
              ·
                refine ⟨9259036910579938803828365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172691273719959202552243 9259036910579938803828365)
                ·
                  refine ⟨3472138841467477051435637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9259036910579938803828365 3472138841467477051435637)
                  ·
                    refine ⟨325513016387575973572091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3472138841467477051435637 325513016387575973572091)
                    ·
                      rfl

theorem cell23_1901803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 5].length) (baseStart_1901803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901803 prefixEnd_1901803 := by exact prefixLift 1901803
  have htrace : WordTrace (prefixWord ++ tailWord_1901803) baseStart_1901803 baseEnd_1901803 := by
    simpa [prefixWord, tailWord_1901803, baseEnd_1901803] using wordTrace_append hprefix tailTrace_1901803
  have hstable : (prefixWord ++ tailWord_1901803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901803).length < 2 ^ (prefixWord ++ tailWord_1901803).sum := by decide
  have hdescent : baseEnd_1901803 < baseStart_1901803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901850 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1901850 : Nat := 118140960795 + 1901850 * 2 ^ 59
def prefixEnd_1901850 : Nat := 4983230072969 + 3 ^ 40 * 1901850 * 2
def baseEnd_1901850 : Nat := 325521060917829745609519

theorem tailTrace_1901850 : CollatzResearch.WordTrace tailWord_1901850 prefixEnd_1901850 325521060917829745609519 := by
  unfold tailWord_1901850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17341542039982433741413751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46244112106619823310436669 17341542039982433741413751)
  ·
    refine ⟨26012313059973650612120627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17341542039982433741413751 26012313059973650612120627)
    ·
      refine ⟨39018469589960475918180941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26012313059973650612120627 39018469589960475918180941)
      ·
        refine ⟨14631926096235178469317853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39018469589960475918180941 14631926096235178469317853)
        ·
          refine ⟨5486972286088191925994195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14631926096235178469317853 5486972286088191925994195)
          ·
            refine ⟨8230458429132287888991293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486972286088191925994195 8230458429132287888991293)
            ·
              refine ⟨3086421910924607958371735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8230458429132287888991293 3086421910924607958371735)
              ·
                refine ⟨4629632866386911937557603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086421910924607958371735 4629632866386911937557603)
                ·
                  refine ⟨6944449299580367906336405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629632866386911937557603 6944449299580367906336405)
                  ·
                    refine ⟨325521060917829745609519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6944449299580367906336405 325521060917829745609519)
                    ·
                      rfl

theorem cell23_1901850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1901850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901850 prefixEnd_1901850 := by exact prefixLift 1901850
  have htrace : WordTrace (prefixWord ++ tailWord_1901850) baseStart_1901850 baseEnd_1901850 := by
    simpa [prefixWord, tailWord_1901850, baseEnd_1901850] using wordTrace_append hprefix tailTrace_1901850
  have hstable : (prefixWord ++ tailWord_1901850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901850).length < 2 ^ (prefixWord ++ tailWord_1901850).sum := by decide
  have hdescent : baseEnd_1901850 < baseStart_1901850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901877 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1901877 : Nat := 118140960795 + 1901877 * 2 ^ 59
def prefixEnd_1901877 : Nat := 4983230072969 + 3 ^ 40 * 1901877 * 2
def baseEnd_1901877 : Nat := 976577046731160631190933

theorem tailTrace_1901877 : CollatzResearch.WordTrace tailWord_1901877 prefixEnd_1901877 976577046731160631190933 := by
  unfold tailWord_1901877
  simp only [CollatzResearch.WordTrace]
  refine ⟨69367152930831918576887885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46244768620554612384591923 69367152930831918576887885)
  ·
    refine ⟨26012682349061969466332957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69367152930831918576887885 26012682349061969466332957)
    ·
      refine ⟨9754755880898238549874859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26012682349061969466332957 9754755880898238549874859)
      ·
        refine ⟨14632133821347357824812289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754755880898238549874859 14632133821347357824812289)
        ·
          refine ⟨10974100366010518368609217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14632133821347357824812289 10974100366010518368609217)
          ·
            refine ⟨8230575274507888776456913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10974100366010518368609217 8230575274507888776456913)
            ·
              refine ⟨6172931455880916582342685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8230575274507888776456913 6172931455880916582342685)
              ·
                refine ⟨2314849295955343718378507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6172931455880916582342685 2314849295955343718378507)
                ·
                  refine ⟨3472273943933015577567761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314849295955343718378507 3472273943933015577567761)
                  ·
                    refine ⟨2604205457949761683175821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472273943933015577567761 2604205457949761683175821)
                    ·
                      refine ⟨976577046731160631190933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2604205457949761683175821 976577046731160631190933)
                      ·
                        rfl

theorem cell23_1901877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1901877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901877 prefixEnd_1901877 := by exact prefixLift 1901877
  have htrace : WordTrace (prefixWord ++ tailWord_1901877) baseStart_1901877 baseEnd_1901877 := by
    simpa [prefixWord, tailWord_1901877, baseEnd_1901877] using wordTrace_append hprefix tailTrace_1901877
  have hstable : (prefixWord ++ tailWord_1901877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901877).length < 2 ^ (prefixWord ++ tailWord_1901877).sum := by decide
  have hdescent : baseEnd_1901877 < baseStart_1901877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901901 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1901901 : Nat := 118140960795 + 1901901 * 2 ^ 59
def prefixEnd_1901901 : Nat := 4983230072969 + 3 ^ 40 * 1901901 * 2
def baseEnd_1901901 : Nat := 325529790088956179096941

theorem tailTrace_1901901 : CollatzResearch.WordTrace tailWord_1901901 prefixEnd_1901901 325529790088956179096941 := by
  unfold tailWord_1901901
  simp only [CollatzResearch.WordTrace]
  refine ⟨69368028282744970675761557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46245352188496647117174371 69368028282744970675761557)
  ·
    refine ⟨3251626325753670500426323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69368028282744970675761557 3251626325753670500426323)
    ·
      refine ⟨4877439488630505750639485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3251626325753670500426323 4877439488630505750639485)
      ·
        refine ⟨1829039808236439656489807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4877439488630505750639485 1829039808236439656489807)
        ·
          refine ⟨2743559712354659484734711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829039808236439656489807 2743559712354659484734711)
          ·
            refine ⟨4115339568531989227102067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743559712354659484734711 4115339568531989227102067)
            ·
              refine ⟨6173009352797983840653101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115339568531989227102067 6173009352797983840653101)
              ·
                refine ⟨2314878507299243940244913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173009352797983840653101 2314878507299243940244913)
                ·
                  refine ⟨1736158880474432955183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314878507299243940244913 1736158880474432955183685)
                  ·
                    refine ⟨325529790088956179096941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736158880474432955183685 325529790088956179096941)
                    ·
                      rfl

theorem cell23_1901901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1901901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901901 prefixEnd_1901901 := by exact prefixLift 1901901
  have htrace : WordTrace (prefixWord ++ tailWord_1901901) baseStart_1901901 baseEnd_1901901 := by
    simpa [prefixWord, tailWord_1901901, baseEnd_1901901] using wordTrace_append hprefix tailTrace_1901901
  have hstable : (prefixWord ++ tailWord_1901901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901901).length < 2 ^ (prefixWord ++ tailWord_1901901).sum := by decide
  have hdescent : baseEnd_1901901 < baseStart_1901901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901907 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 3]
def baseStart_1901907 : Nat := 118140960795 + 1901907 * 2 ^ 59
def prefixEnd_1901907 : Nat := 4983230072969 + 3 ^ 40 * 1901907 * 2
def baseEnd_1901907 : Nat := 976592451150795513815795

theorem tailTrace_1901907 : CollatzResearch.WordTrace tailWord_1901907 prefixEnd_1901907 976592451150795513815795 := by
  unfold tailWord_1901907
  simp only [CollatzResearch.WordTrace]
  refine ⟨69368247120723233700479975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46245498080482155800319983 69368247120723233700479975)
  ·
    refine ⟨104052370681084850550719963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69368247120723233700479975 104052370681084850550719963)
    ·
      refine ⟨156078556021627275826079945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104052370681084850550719963 156078556021627275826079945)
      ·
        refine ⟨117058917016220456869559959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156078556021627275826079945 117058917016220456869559959)
        ·
          refine ⟨175588375524330685304339939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117058917016220456869559959 175588375524330685304339939)
          ·
            refine ⟨263382563286496027956509909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175588375524330685304339939 263382563286496027956509909)
            ·
              refine ⟨6173028827027250655230701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263382563286496027956509909 6173028827027250655230701)
              ·
                refine ⟨2314885810135218995711513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173028827027250655230701 2314885810135218995711513)
                ·
                  refine ⟨1736164357601414246783635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314885810135218995711513 1736164357601414246783635)
                  ·
                    refine ⟨2604246536402121370175453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736164357601414246783635 2604246536402121370175453)
                    ·
                      refine ⟨976592451150795513815795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2604246536402121370175453 976592451150795513815795)
                      ·
                        rfl

theorem cell23_1901907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 3].length) (baseStart_1901907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901907 prefixEnd_1901907 := by exact prefixLift 1901907
  have htrace : WordTrace (prefixWord ++ tailWord_1901907) baseStart_1901907 baseEnd_1901907 := by
    simpa [prefixWord, tailWord_1901907, baseEnd_1901907] using wordTrace_append hprefix tailTrace_1901907
  have hstable : (prefixWord ++ tailWord_1901907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901907).length < 2 ^ (prefixWord ++ tailWord_1901907).sum := by decide
  have hdescent : baseEnd_1901907 < baseStart_1901907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901941 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1901941 : Nat := 118140960795 + 1901941 * 2 ^ 59
def prefixEnd_1901941 : Nat := 4983230072969 + 3 ^ 40 * 1901941 * 2
def baseEnd_1901941 : Nat := 976609909493048380790639

theorem tailTrace_1901941 : CollatzResearch.WordTrace tailWord_1901941 prefixEnd_1901941 976609909493048380790639 := by
  unfold tailWord_1901941
  simp only [CollatzResearch.WordTrace]
  refine ⟨69369487202600057507217677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46246324801733371671478451 69369487202600057507217677)
  ·
    refine ⟨26013557700975021565206629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69369487202600057507217677 26013557700975021565206629)
    ·
      refine ⟨4877542068932816543476243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26013557700975021565206629 4877542068932816543476243)
      ·
        refine ⟨7316313103399224815214365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877542068932816543476243 7316313103399224815214365)
        ·
          refine ⟨2743617413774709305705387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7316313103399224815214365 2743617413774709305705387)
          ·
            refine ⟨4115426120662063958558081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743617413774709305705387 4115426120662063958558081)
            ·
              refine ⟨3086569590496547968918561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115426120662063958558081 3086569590496547968918561)
              ·
                refine ⟨2314927192872410976688921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086569590496547968918561 2314927192872410976688921)
                ·
                  refine ⟨1736195394654308232516691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314927192872410976688921 1736195394654308232516691)
                  ·
                    refine ⟨2604293091981462348775037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736195394654308232516691 2604293091981462348775037)
                    ·
                      refine ⟨976609909493048380790639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2604293091981462348775037 976609909493048380790639)
                      ·
                        rfl

theorem cell23_1901941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1901941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901941 prefixEnd_1901941 := by exact prefixLift 1901941
  have htrace : WordTrace (prefixWord ++ tailWord_1901941) baseStart_1901941 baseEnd_1901941 := by
    simpa [prefixWord, tailWord_1901941, baseEnd_1901941] using wordTrace_append hprefix tailTrace_1901941
  have hstable : (prefixWord ++ tailWord_1901941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901941).length < 2 ^ (prefixWord ++ tailWord_1901941).sum := by decide
  have hdescent : baseEnd_1901941 < baseStart_1901941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901960 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1901960 : Nat := 118140960795 + 1901960 * 2 ^ 59
def prefixEnd_1901960 : Nat := 4983230072969 + 3 ^ 40 * 1901960 * 2
def baseEnd_1901960 : Nat := 976619665625483806453051

theorem tailTrace_1901960 : CollatzResearch.WordTrace tailWord_1901960 prefixEnd_1901960 976619665625483806453051 := by
  unfold tailWord_1901960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685090094765611876079667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46246786793020815834772889 34685090094765611876079667)
  ·
    refine ⟨52027635142148417814119501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34685090094765611876079667 52027635142148417814119501)
    ·
      refine ⟨19510363178305656680294813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52027635142148417814119501 19510363178305656680294813)
      ·
        refine ⟨7316386191864621255110555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19510363178305656680294813 7316386191864621255110555)
        ·
          refine ⟨10974579287796931882665833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316386191864621255110555 10974579287796931882665833)
          ·
            refine ⟨8230934465847698911999375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10974579287796931882665833 8230934465847698911999375)
            ·
              refine ⟨12346401698771548367999063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230934465847698911999375 12346401698771548367999063)
              ·
                refine ⟨18519602548157322551998595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346401698771548367999063 18519602548157322551998595)
                ·
                  refine ⟨27779403822235983827997893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18519602548157322551998595 27779403822235983827997893)
                  ·
                    refine ⟨5208638216669246967749605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27779403822235983827997893 5208638216669246967749605)
                    ·
                      refine ⟨976619665625483806453051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5208638216669246967749605 976619665625483806453051)
                      ·
                        rfl

theorem cell23_1901960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1901960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901960 prefixEnd_1901960 := by exact prefixLift 1901960
  have htrace : WordTrace (prefixWord ++ tailWord_1901960) baseStart_1901960 baseEnd_1901960 := by
    simpa [prefixWord, tailWord_1901960, baseEnd_1901960] using wordTrace_append hprefix tailTrace_1901960
  have hstable : (prefixWord ++ tailWord_1901960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901960).length < 2 ^ (prefixWord ++ tailWord_1901960).sum := by decide
  have hdescent : baseEnd_1901960 < baseStart_1901960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901964 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_1901964 : Nat := 118140960795 + 1901964 * 2 ^ 59
def prefixEnd_1901964 : Nat := 4983230072969 + 3 ^ 40 * 1901964 * 2
def baseEnd_1901964 : Nat := 976621719548101790803033

theorem tailTrace_1901964 : CollatzResearch.WordTrace tailWord_1901964 prefixEnd_1901964 976621719548101790803033 := by
  unfold tailWord_1901964
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685163040758366217652473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46246884054344488290203297 34685163040758366217652473)
  ·
    refine ⟨26013872280568774663239355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34685163040758366217652473 26013872280568774663239355)
    ·
      refine ⟨39020808420853161994859033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26013872280568774663239355 39020808420853161994859033)
      ·
        refine ⟨29265606315639871496144275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39020808420853161994859033 29265606315639871496144275)
        ·
          refine ⟨43898409473459807244216413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29265606315639871496144275 43898409473459807244216413)
          ·
            refine ⟨16461903552547427716581155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43898409473459807244216413 16461903552547427716581155)
            ·
              refine ⟨24692855328821141574871733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16461903552547427716581155 24692855328821141574871733)
              ·
                refine ⟨2314955187076982022644225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24692855328821141574871733 2314955187076982022644225)
                ·
                  refine ⟨1736216390307736516983169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314955187076982022644225 1736216390307736516983169)
                  ·
                    refine ⟨1302162292730802387737377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1736216390307736516983169 1302162292730802387737377)
                    ·
                      refine ⟨976621719548101790803033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302162292730802387737377 976621719548101790803033)
                      ·
                        rfl

theorem cell23_1901964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_1901964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901964 prefixEnd_1901964 := by exact prefixLift 1901964
  have htrace : WordTrace (prefixWord ++ tailWord_1901964) baseStart_1901964 baseEnd_1901964 := by
    simpa [prefixWord, tailWord_1901964, baseEnd_1901964] using wordTrace_append hprefix tailTrace_1901964
  have hstable : (prefixWord ++ tailWord_1901964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901964).length < 2 ^ (prefixWord ++ tailWord_1901964).sum := by decide
  have hdescent : baseEnd_1901964 < baseStart_1901964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901987 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 5]
def baseStart_1901987 : Nat := 118140960795 + 1901987 * 2 ^ 59
def prefixEnd_1901987 : Nat := 4983230072969 + 3 ^ 40 * 1901987 * 2
def baseEnd_1901987 : Nat := 108514836622572800090603

theorem tailTrace_1901987 : CollatzResearch.WordTrace tailWord_1901987 prefixEnd_1901987 108514836622572800090603 := by
  unfold tailWord_1901987
  simp only [CollatzResearch.WordTrace]
  refine ⟨69371164960433407363392215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46247443306955604908928143 69371164960433407363392215)
  ·
    refine ⟨104056747440650111045088323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69371164960433407363392215 104056747440650111045088323)
    ·
      refine ⟨156085121160975166567632485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104056747440650111045088323 156085121160975166567632485)
      ·
        refine ⟨29265960217682843731431091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156085121160975166567632485 29265960217682843731431091)
        ·
          refine ⟨43898940326524265597146637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29265960217682843731431091 43898940326524265597146637)
          ·
            refine ⟨16462102622446599598929989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43898940326524265597146637 16462102622446599598929989)
            ·
              refine ⟨3086644241708737424799373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16462102622446599598929989 3086644241708737424799373)
              ·
                refine ⟨1157491590640776534299765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3086644241708737424799373 1157491590640776534299765)
                ·
                  refine ⟨108514836622572800090603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157491590640776534299765 108514836622572800090603)
                  ·
                    rfl

theorem cell23_1901987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 5].length) (baseStart_1901987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1901987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1901987 prefixEnd_1901987 := by exact prefixLift 1901987
  have htrace : WordTrace (prefixWord ++ tailWord_1901987) baseStart_1901987 baseEnd_1901987 := by
    simpa [prefixWord, tailWord_1901987, baseEnd_1901987] using wordTrace_append hprefix tailTrace_1901987
  have hstable : (prefixWord ++ tailWord_1901987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901987).length < 2 ^ (prefixWord ++ tailWord_1901987).sum := by decide
  have hdescent : baseEnd_1901987 < baseStart_1901987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902037 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1902037 : Nat := 118140960795 + 1902037 * 2 ^ 59
def prefixEnd_1902037 : Nat := 4983230072969 + 3 ^ 40 * 1902037 * 2
def baseEnd_1902037 : Nat := 976659203635880005190197

theorem tailTrace_1902037 : CollatzResearch.WordTrace tailWord_1902037 prefixEnd_1902037 976659203635880005190197 := by
  unfold tailWord_1902037
  simp only [CollatzResearch.WordTrace]
  refine ⟨69372988610252265902712365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46248659073501510601808243 69372988610252265902712365)
  ·
    refine ⟨26014870728844599713517137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69372988610252265902712365 26014870728844599713517137)
    ·
      refine ⟨19511153046633449785137853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26014870728844599713517137 19511153046633449785137853)
      ·
        refine ⟨7316682392487543669426695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19511153046633449785137853 7316682392487543669426695)
        ·
          refine ⟨10975023588731315504140043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7316682392487543669426695 10975023588731315504140043)
          ·
            refine ⟨16462535383096973256210065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10975023588731315504140043 16462535383096973256210065)
            ·
              refine ⟨12346901537322729942157549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16462535383096973256210065 12346901537322729942157549)
              ·
                refine ⟨4630088076496023728309081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12346901537322729942157549 4630088076496023728309081)
                ·
                  refine ⟨3472566057372017796231811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4630088076496023728309081 3472566057372017796231811)
                  ·
                    refine ⟨5208849086058026694347717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3472566057372017796231811 5208849086058026694347717)
                    ·
                      refine ⟨976659203635880005190197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5208849086058026694347717 976659203635880005190197)
                      ·
                        rfl

theorem cell23_1902037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1902037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902037 prefixEnd_1902037 := by exact prefixLift 1902037
  have htrace : WordTrace (prefixWord ++ tailWord_1902037) baseStart_1902037 baseEnd_1902037 := by
    simpa [prefixWord, tailWord_1902037, baseEnd_1902037] using wordTrace_append hprefix tailTrace_1902037
  have hstable : (prefixWord ++ tailWord_1902037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902037).length < 2 ^ (prefixWord ++ tailWord_1902037).sum := by decide
  have hdescent : baseEnd_1902037 < baseStart_1902037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902064 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_1902064 : Nat := 118140960795 + 1902064 * 2 ^ 59
def prefixEnd_1902064 : Nat := 4983230072969 + 3 ^ 40 * 1902064 * 2
def baseEnd_1902064 : Nat := 325557689204517133184191

theorem tailTrace_1902064 : CollatzResearch.WordTrace tailWord_1902064 prefixEnd_1902064 325557689204517133184191 := by
  unfold tailWord_1902064
  simp only [CollatzResearch.WordTrace]
  refine ⟨34686986690577224756972623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46249315587436299675963497 34686986690577224756972623)
  ·
    refine ⟨52030480035865837135458935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34686986690577224756972623 52030480035865837135458935)
    ·
      refine ⟨78045720053798755703188403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52030480035865837135458935 78045720053798755703188403)
      ·
        refine ⟨117068580080698133554782605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78045720053798755703188403 117068580080698133554782605)
        ·
          refine ⟨43900717530261800083043477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117068580080698133554782605 43900717530261800083043477)
          ·
            refine ⟨2057846134231021878892663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43900717530261800083043477 2057846134231021878892663)
            ·
              refine ⟨3086769201346532818338995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057846134231021878892663 3086769201346532818338995)
              ·
                refine ⟨4630153802019799227508493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3086769201346532818338995 4630153802019799227508493)
                ·
                  refine ⟨1736307675757424710315685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4630153802019799227508493 1736307675757424710315685)
                  ·
                    refine ⟨325557689204517133184191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736307675757424710315685 325557689204517133184191)
                    ·
                      rfl

theorem cell23_1902064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_1902064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902064 prefixEnd_1902064 := by exact prefixLift 1902064
  have htrace : WordTrace (prefixWord ++ tailWord_1902064) baseStart_1902064 baseEnd_1902064 := by
    simpa [prefixWord, tailWord_1902064, baseEnd_1902064] using wordTrace_append hprefix tailTrace_1902064
  have hstable : (prefixWord ++ tailWord_1902064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902064).length < 2 ^ (prefixWord ++ tailWord_1902064).sum := by decide
  have hdescent : baseEnd_1902064 < baseStart_1902064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902077 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 6]
def baseStart_1902077 : Nat := 118140960795 + 1902077 * 2 ^ 59
def prefixEnd_1902077 : Nat := 4983230072969 + 3 ^ 40 * 1902077 * 2
def baseEnd_1902077 : Nat := 108519971429117760965557

theorem tailTrace_1902077 : CollatzResearch.WordTrace tailWord_1902077 prefixEnd_1902077 108519971429117760965557 := by
  unfold tailWord_1902077
  simp only [CollatzResearch.WordTrace]
  refine ⟨69374447530107352734168485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46249631686738235156112323 69374447530107352734168485)
  ·
    refine ⟨13007708911895128637656591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69374447530107352734168485 13007708911895128637656591)
    ·
      refine ⟨19511563367842692956484887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13007708911895128637656591 19511563367842692956484887)
      ·
        refine ⟨29267345051764039434727331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19511563367842692956484887 29267345051764039434727331)
        ·
          refine ⟨43901017577646059152090997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29267345051764039434727331 43901017577646059152090997)
          ·
            refine ⟨4115720397904318045508531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43901017577646059152090997 4115720397904318045508531)
            ·
              refine ⟨6173580596856477068262797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115720397904318045508531 6173580596856477068262797)
              ·
                refine ⟨2315092723821178900598549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6173580596856477068262797 2315092723821178900598549)
                ·
                  refine ⟨108519971429117760965557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2315092723821178900598549 108519971429117760965557)
                  ·
                    rfl

theorem cell23_1902077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_1902077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902077 prefixEnd_1902077 := by exact prefixLift 1902077
  have htrace : WordTrace (prefixWord ++ tailWord_1902077) baseStart_1902077 baseEnd_1902077 := by
    simpa [prefixWord, tailWord_1902077, baseEnd_1902077] using wordTrace_append hprefix tailTrace_1902077
  have hstable : (prefixWord ++ tailWord_1902077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902077).length < 2 ^ (prefixWord ++ tailWord_1902077).sum := by decide
  have hdescent : baseEnd_1902077 < baseStart_1902077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902115 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 1, 4]
def baseStart_1902115 : Nat := 118140960795 + 1902115 * 2 ^ 59
def prefixEnd_1902115 : Nat := 4983230072969 + 3 ^ 40 * 1902115 * 2
def baseEnd_1902115 : Nat := 325566418375643566671613

theorem tailTrace_1902115 : CollatzResearch.WordTrace tailWord_1902115 prefixEnd_1902115 325566418375643566671613 := by
  unfold tailWord_1902115
  simp only [CollatzResearch.WordTrace]
  refine ⟨69375833503969685224051799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46250555669313123482701199 69375833503969685224051799)
  ·
    refine ⟨104063750255954527836077699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69375833503969685224051799 104063750255954527836077699)
    ·
      refine ⟨156095625383931791754116549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104063750255954527836077699 156095625383931791754116549)
      ·
        refine ⟨29267929759487210953896853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156095625383931791754116549 29267929759487210953896853)
        ·
          refine ⟨1371934207475963013463915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29267929759487210953896853 1371934207475963013463915)
          ·
            refine ⟨2057901311213944520195873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371934207475963013463915 2057901311213944520195873)
            ·
              refine ⟨1543425983410458390146905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057901311213944520195873 1543425983410458390146905)
              ·
                refine ⟨1157569487557843792610179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543425983410458390146905 1157569487557843792610179)
                ·
                  refine ⟨1736354231336765688915269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157569487557843792610179 1736354231336765688915269)
                  ·
                    refine ⟨325566418375643566671613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736354231336765688915269 325566418375643566671613)
                    ·
                      rfl

theorem cell23_1902115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 4].length) (baseStart_1902115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902115 prefixEnd_1902115 := by exact prefixLift 1902115
  have htrace : WordTrace (prefixWord ++ tailWord_1902115) baseStart_1902115 baseEnd_1902115 := by
    simpa [prefixWord, tailWord_1902115, baseEnd_1902115] using wordTrace_append hprefix tailTrace_1902115
  have hstable : (prefixWord ++ tailWord_1902115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902115).length < 2 ^ (prefixWord ++ tailWord_1902115).sum := by decide
  have hdescent : baseEnd_1902115 < baseStart_1902115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902137 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_1902137 : Nat := 118140960795 + 1902137 * 2 ^ 59
def prefixEnd_1902137 : Nat := 4983230072969 + 3 ^ 40 * 1902137 * 2
def baseEnd_1902137 : Nat := 325570183900443204646579

theorem tailTrace_1902137 : CollatzResearch.WordTrace tailWord_1902137 prefixEnd_1902137 325570183900443204646579 := by
  unfold tailWord_1902137
  simp only [CollatzResearch.WordTrace]
  refine ⟨69376635909889982981352665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46251090606593321987568443 69376635909889982981352665)
  ·
    refine ⟨52032476932417487236014499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69376635909889982981352665 52032476932417487236014499)
    ·
      refine ⟨78048715398626230854021749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52032476932417487236014499 78048715398626230854021749)
      ·
        refine ⟨7317067068621209142564539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78048715398626230854021749 7317067068621209142564539)
        ·
          refine ⟨10975600602931813713846809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317067068621209142564539 10975600602931813713846809)
          ·
            refine ⟨8231700452198860285385107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10975600602931813713846809 8231700452198860285385107)
            ·
              refine ⟨12347550678298290428077661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231700452198860285385107 12347550678298290428077661)
              ·
                refine ⟨4630331504361858910529123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12347550678298290428077661 4630331504361858910529123)
                ·
                  refine ⟨6945497256542788365793685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630331504361858910529123 6945497256542788365793685)
                  ·
                    refine ⟨325570183900443204646579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6945497256542788365793685 325570183900443204646579)
                    ·
                      rfl

theorem cell23_1902137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_1902137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902137 prefixEnd_1902137 := by exact prefixLift 1902137
  have htrace : WordTrace (prefixWord ++ tailWord_1902137) baseStart_1902137 baseEnd_1902137 := by
    simpa [prefixWord, tailWord_1902137, baseEnd_1902137] using wordTrace_append hprefix tailTrace_1902137
  have hstable : (prefixWord ++ tailWord_1902137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902137).length < 2 ^ (prefixWord ++ tailWord_1902137).sum := by decide
  have hdescent : baseEnd_1902137 < baseStart_1902137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902198 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1902198 : Nat := 118140960795 + 1902198 * 2 ^ 59
def prefixEnd_1902198 : Nat := 4983230072969 + 3 ^ 40 * 1902198 * 2
def baseEnd_1902198 : Nat := 976741874021253875276957

theorem tailTrace_1902198 : CollatzResearch.WordTrace tailWord_1902198 prefixEnd_1902198 976741874021253875276957 := by
  unfold tailWord_1902198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336178797666811899957703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46252573841779326932882165 4336178797666811899957703)
  ·
    refine ⟨6504268196500217849936555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4336178797666811899957703 6504268196500217849936555)
    ·
      refine ⟨9756402294750326774904833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6504268196500217849936555 9756402294750326774904833)
      ·
        refine ⟨7317301721062745081178625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9756402294750326774904833 7317301721062745081178625)
        ·
          refine ⟨5487976290797058810883969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7317301721062745081178625 5487976290797058810883969)
          ·
            refine ⟨4115982218097794108162977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5487976290797058810883969 4115982218097794108162977)
            ·
              refine ⟨3086986663573345581122233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115982218097794108162977 3086986663573345581122233)
              ·
                refine ⟨2315239997680009185841675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3086986663573345581122233 2315239997680009185841675)
                ·
                  refine ⟨3472859996520013778762513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315239997680009185841675 3472859996520013778762513)
                  ·
                    refine ⟨2604644997390010334071885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3472859996520013778762513 2604644997390010334071885)
                    ·
                      refine ⟨976741874021253875276957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2604644997390010334071885 976741874021253875276957)
                      ·
                        rfl

theorem cell23_1902198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1902198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902198 prefixEnd_1902198 := by exact prefixLift 1902198
  have htrace : WordTrace (prefixWord ++ tailWord_1902198) baseStart_1902198 baseEnd_1902198 := by
    simpa [prefixWord, tailWord_1902198, baseEnd_1902198] using wordTrace_append hprefix tailTrace_1902198
  have hstable : (prefixWord ++ tailWord_1902198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902198).length < 2 ^ (prefixWord ++ tailWord_1902198).sum := by decide
  have hdescent : baseEnd_1902198 < baseStart_1902198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902212 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1902212 : Nat := 118140960795 + 1902212 * 2 ^ 59
def prefixEnd_1902212 : Nat := 4983230072969 + 3 ^ 40 * 1902212 * 2
def baseEnd_1902212 : Nat := 976749062750416820501893

theorem tailTrace_1902212 : CollatzResearch.WordTrace tailWord_1902212 prefixEnd_1902212 976749062750416820501893 := by
  unfold tailWord_1902212
  simp only [CollatzResearch.WordTrace]
  refine ⟨34689685692309135395166445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46252914256412180526888593 34689685692309135395166445)
  ·
    refine ⟨13008632134615925773187417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34689685692309135395166445 13008632134615925773187417)
    ·
      refine ⟨9756474100961944329890563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13008632134615925773187417 9756474100961944329890563)
      ·
        refine ⟨14634711151442916494835845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756474100961944329890563 14634711151442916494835845)
        ·
          refine ⟨2744008340895546842781721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14634711151442916494835845 2744008340895546842781721)
          ·
            refine ⟨2058006255671660132086291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744008340895546842781721 2058006255671660132086291)
            ·
              refine ⟨3087009383507490198129437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058006255671660132086291 3087009383507490198129437)
              ·
                refine ⟨1157628518815308824298539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3087009383507490198129437 1157628518815308824298539)
                ·
                  refine ⟨1736442778222963236447809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157628518815308824298539 1736442778222963236447809)
                  ·
                    refine ⟨1302332083667222427335857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1736442778222963236447809 1302332083667222427335857)
                    ·
                      refine ⟨976749062750416820501893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302332083667222427335857 976749062750416820501893)
                      ·
                        rfl

theorem cell23_1902212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1902212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902212 prefixEnd_1902212 := by exact prefixLift 1902212
  have htrace : WordTrace (prefixWord ++ tailWord_1902212) baseStart_1902212 baseEnd_1902212 := by
    simpa [prefixWord, tailWord_1902212, baseEnd_1902212] using wordTrace_append hprefix tailTrace_1902212
  have hstable : (prefixWord ++ tailWord_1902212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902212).length < 2 ^ (prefixWord ++ tailWord_1902212).sum := by decide
  have hdescent : baseEnd_1902212 < baseStart_1902212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902237 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1902237 : Nat := 118140960795 + 1902237 * 2 ^ 59
def prefixEnd_1902237 : Nat := 4983230072969 + 3 ^ 40 * 1902237 * 2
def baseEnd_1902237 : Nat := 976761899766779222689277

theorem tailTrace_1902237 : CollatzResearch.WordTrace tailWord_1902237 prefixEnd_1902237 976761899766779222689277 := by
  unfold tailWord_1902237
  simp only [CollatzResearch.WordTrace]
  refine ⟨69380283209527700059992965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46253522139685133373328643 69380283209527700059992965)
  ·
    refine ⟨13008803101786443761248681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69380283209527700059992965 13008803101786443761248681)
    ·
      refine ⟨9756602326339832820936511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13008803101786443761248681 9756602326339832820936511)
      ·
        refine ⟨14634903489509749231404767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756602326339832820936511 14634903489509749231404767)
        ·
          refine ⟨21952355234264623847107151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14634903489509749231404767 21952355234264623847107151)
          ·
            refine ⟨32928532851396935770660727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21952355234264623847107151 32928532851396935770660727)
            ·
              refine ⟨49392799277095403655991091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32928532851396935770660727 49392799277095403655991091)
              ·
                refine ⟨74089198915643105483986637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49392799277095403655991091 74089198915643105483986637)
                ·
                  refine ⟨27783449593366164556494989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74089198915643105483986637 27783449593366164556494989)
                  ·
                    refine ⟨10418793597512311708685621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27783449593366164556494989 10418793597512311708685621)
                    ·
                      refine ⟨976761899766779222689277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10418793597512311708685621 976761899766779222689277)
                      ·
                        rfl

theorem cell23_1902237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1902237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902237 prefixEnd_1902237 := by exact prefixLift 1902237
  have htrace : WordTrace (prefixWord ++ tailWord_1902237) baseStart_1902237 baseEnd_1902237 := by
    simpa [prefixWord, tailWord_1902237, baseEnd_1902237] using wordTrace_append hprefix tailTrace_1902237
  have hstable : (prefixWord ++ tailWord_1902237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902237).length < 2 ^ (prefixWord ++ tailWord_1902237).sum := by decide
  have hdescent : baseEnd_1902237 < baseStart_1902237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902321 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_1902321 : Nat := 118140960795 + 1902321 * 2 ^ 59
def prefixEnd_1902321 : Nat := 4983230072969 + 3 ^ 40 * 1902321 * 2
def baseEnd_1902321 : Nat := 325601677380585631346297

theorem tailTrace_1902321 : CollatzResearch.WordTrace tailWord_1902321 prefixEnd_1902321 325601677380585631346297 := by
  unfold tailWord_1902321
  simp only [CollatzResearch.WordTrace]
  refine ⟨69383346941223382406050817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46255564627482254937367211 69383346941223382406050817)
  ·
    refine ⟨52037510205917536804538113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69383346941223382406050817 52037510205917536804538113)
    ·
      refine ⟨39028132654438152603403585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52037510205917536804538113 39028132654438152603403585)
      ·
        refine ⟨29271099490828614452552689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39028132654438152603403585 29271099490828614452552689)
        ·
          refine ⟨21953324618121460839414517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29271099490828614452552689 21953324618121460839414517)
          ·
            refine ⟨2058124182948886953695111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21953324618121460839414517 2058124182948886953695111)
            ·
              refine ⟨3087186274423330430542667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058124182948886953695111 3087186274423330430542667)
              ·
                refine ⟨4630779411634995645814001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087186274423330430542667 4630779411634995645814001)
                ·
                  refine ⟨3473084558726246734360501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4630779411634995645814001 3473084558726246734360501)
                  ·
                    refine ⟨325601677380585631346297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3473084558726246734360501 325601677380585631346297)
                    ·
                      rfl

theorem cell23_1902321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_1902321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902321 prefixEnd_1902321 := by exact prefixLift 1902321
  have htrace : WordTrace (prefixWord ++ tailWord_1902321) baseStart_1902321 baseEnd_1902321 := by
    simpa [prefixWord, tailWord_1902321, baseEnd_1902321] using wordTrace_append hprefix tailTrace_1902321
  have hstable : (prefixWord ++ tailWord_1902321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902321).length < 2 ^ (prefixWord ++ tailWord_1902321).sum := by decide
  have hdescent : baseEnd_1902321 < baseStart_1902321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902385 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 1, 4]
def baseStart_1902385 : Nat := 118140960795 + 1902385 * 2 ^ 59
def prefixEnd_1902385 : Nat := 4983230072969 + 3 ^ 40 * 1902385 * 2
def baseEnd_1902385 : Nat := 325612631634548214546199

theorem tailTrace_1902385 : CollatzResearch.WordTrace tailWord_1902385 prefixEnd_1902385 325612631634548214546199 := by
  unfold tailWord_1902385
  simp only [CollatzResearch.WordTrace]
  refine ⟨69385681212991521336380609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46257120808661014224253739 69385681212991521336380609)
  ·
    refine ⟨52039260909743641002285457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69385681212991521336380609 52039260909743641002285457)
    ·
      refine ⟨39029445682307730751714093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52039260909743641002285457 39029445682307730751714093)
      ·
        refine ⟨14636042130865399031892785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39029445682307730751714093 14636042130865399031892785)
        ·
          refine ⟨10977031598149049273919589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14636042130865399031892785 10977031598149049273919589)
          ·
            refine ⟨2058193424652946738859923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10977031598149049273919589 2058193424652946738859923)
            ·
              refine ⟨3087290136979420108289885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058193424652946738859923 3087290136979420108289885)
              ·
                refine ⟨1157733801367282540608707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3087290136979420108289885 1157733801367282540608707)
                ·
                  refine ⟨1736600702050923810913061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157733801367282540608707 1736600702050923810913061)
                  ·
                    refine ⟨325612631634548214546199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736600702050923810913061 325612631634548214546199)
                    ·
                      rfl

theorem cell23_1902385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_1902385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902385 prefixEnd_1902385 := by exact prefixLift 1902385
  have htrace : WordTrace (prefixWord ++ tailWord_1902385) baseStart_1902385 baseEnd_1902385 := by
    simpa [prefixWord, tailWord_1902385, baseEnd_1902385] using wordTrace_append hprefix tailTrace_1902385
  have hstable : (prefixWord ++ tailWord_1902385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902385).length < 2 ^ (prefixWord ++ tailWord_1902385).sum := by decide
  have hdescent : baseEnd_1902385 < baseStart_1902385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902408 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3]
def baseStart_1902408 : Nat := 118140960795 + 1902408 * 2 ^ 59
def prefixEnd_1902408 : Nat := 4983230072969 + 3 ^ 40 * 1902408 * 2
def baseEnd_1902408 : Nat := 976849704958698053650991

theorem tailTrace_1902408 : CollatzResearch.WordTrace tailWord_1902408 prefixEnd_1902408 976849704958698053650991 := by
  unfold tailWord_1902408
  simp only [CollatzResearch.WordTrace]
  refine ⟨34693260045954098132233939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46257680061272130842978585 34693260045954098132233939)
  ·
    refine ⟨52039890068931147198350909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34693260045954098132233939 52039890068931147198350909)
    ·
      refine ⟨19514958775849180199381591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52039890068931147198350909 19514958775849180199381591)
      ·
        refine ⟨29272438163773770299072387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19514958775849180199381591 29272438163773770299072387)
        ·
          refine ⟨43908657245660655448608581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29272438163773770299072387 43908657245660655448608581)
          ·
            refine ⟨8232873233561372896614109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43908657245660655448608581 8232873233561372896614109)
            ·
              refine ⟨3087327462585514836230291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8232873233561372896614109 3087327462585514836230291)
              ·
                refine ⟨4630991193878272254345437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087327462585514836230291 4630991193878272254345437)
                ·
                  refine ⟨1736621697704352095379539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4630991193878272254345437 1736621697704352095379539)
                  ·
                    refine ⟨2604932546556528143069309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736621697704352095379539 2604932546556528143069309)
                    ·
                      refine ⟨976849704958698053650991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2604932546556528143069309 976849704958698053650991)
                      ·
                        rfl

theorem cell23_1902408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_1902408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902408 prefixEnd_1902408 := by exact prefixLift 1902408
  have htrace : WordTrace (prefixWord ++ tailWord_1902408) baseStart_1902408 baseEnd_1902408 := by
    simpa [prefixWord, tailWord_1902408, baseEnd_1902408] using wordTrace_append hprefix tailTrace_1902408
  have hstable : (prefixWord ++ tailWord_1902408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902408).length < 2 ^ (prefixWord ++ tailWord_1902408).sum := by decide
  have hdescent : baseEnd_1902408 < baseStart_1902408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902414 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1902414 : Nat := 118140960795 + 1902414 * 2 ^ 59
def prefixEnd_1902414 : Nat := 4983230072969 + 3 ^ 40 * 1902414 * 2
def baseEnd_1902414 : Nat := 976852785842625030175963

theorem tailTrace_1902414 : CollatzResearch.WordTrace tailWord_1902414 prefixEnd_1902414 976852785842625030175963 := by
  unfold tailWord_1902414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8673342366235807411148287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46257825953257639526124197 8673342366235807411148287)
  ·
    refine ⟨13010013549353711116722431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8673342366235807411148287 13010013549353711116722431)
    ·
      refine ⟨19515020324030566675083647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13010013549353711116722431 19515020324030566675083647)
      ·
        refine ⟨29272530486045850012625471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19515020324030566675083647 29272530486045850012625471)
        ·
          refine ⟨43908795729068775018938207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29272530486045850012625471 43908795729068775018938207)
          ·
            refine ⟨65863193593603162528407311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43908795729068775018938207 65863193593603162528407311)
            ·
              refine ⟨98794790390404743792610967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65863193593603162528407311 98794790390404743792610967)
              ·
                refine ⟨148192185585607115688916451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98794790390404743792610967 148192185585607115688916451)
                ·
                  refine ⟨222288278378410673533374677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148192185585607115688916451 222288278378410673533374677)
                  ·
                    refine ⟨5209881524494000160938469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222288278378410673533374677 5209881524494000160938469)
                    ·
                      refine ⟨976852785842625030175963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5209881524494000160938469 976852785842625030175963)
                      ·
                        rfl

theorem cell23_1902414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1902414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902414 prefixEnd_1902414 := by exact prefixLift 1902414
  have htrace : WordTrace (prefixWord ++ tailWord_1902414) baseStart_1902414 baseEnd_1902414 := by
    simpa [prefixWord, tailWord_1902414, baseEnd_1902414] using wordTrace_append hprefix tailTrace_1902414
  have hstable : (prefixWord ++ tailWord_1902414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902414).length < 2 ^ (prefixWord ++ tailWord_1902414).sum := by decide
  have hdescent : baseEnd_1902414 < baseStart_1902414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902428 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1902428 : Nat := 118140960795 + 1902428 * 2 ^ 59
def prefixEnd_1902428 : Nat := 4983230072969 + 3 ^ 40 * 1902428 * 2
def baseEnd_1902428 : Nat := 325619991523929325133633

theorem tailTrace_1902428 : CollatzResearch.WordTrace tailWord_1902428 prefixEnd_1902428 325619991523929325133633 := by
  unfold tailWord_1902428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34693624775917869840097969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46258166367890493120130625 34693624775917869840097969)
  ·
    refine ⟨26020218581938402380073477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34693624775917869840097969 26020218581938402380073477)
    ·
      refine ⟨4878790984113450446263777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26020218581938402380073477 4878790984113450446263777)
      ·
        refine ⟨3659093238085087834697833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4878790984113450446263777 3659093238085087834697833)
        ·
          refine ⟨2744319928563815876023375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659093238085087834697833 2744319928563815876023375)
          ·
            refine ⟨4116479892845723814035063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744319928563815876023375 4116479892845723814035063)
            ·
              refine ⟨6174719839268585721052595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116479892845723814035063 6174719839268585721052595)
              ·
                refine ⟨9262079758902878581578893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174719839268585721052595 9262079758902878581578893)
                ·
                  refine ⟨3473279909588579468092085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9262079758902878581578893 3473279909588579468092085)
                  ·
                    refine ⟨325619991523929325133633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3473279909588579468092085 325619991523929325133633)
                    ·
                      rfl

theorem cell23_1902428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1902428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902428 prefixEnd_1902428 := by exact prefixLift 1902428
  have htrace : WordTrace (prefixWord ++ tailWord_1902428) baseStart_1902428 baseEnd_1902428 := by
    simpa [prefixWord, tailWord_1902428, baseEnd_1902428] using wordTrace_append hprefix tailTrace_1902428
  have hstable : (prefixWord ++ tailWord_1902428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902428).length < 2 ^ (prefixWord ++ tailWord_1902428).sum := by decide
  have hdescent : baseEnd_1902428 < baseStart_1902428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902431 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1902431 : Nat := 118140960795 + 1902431 * 2 ^ 59
def prefixEnd_1902431 : Nat := 4983230072969 + 3 ^ 40 * 1902431 * 2
def baseEnd_1902431 : Nat := 976861515013751463663385

theorem tailTrace_1902431 : CollatzResearch.WordTrace tailWord_1902431 prefixEnd_1902431 976861515013751463663385 := by
  unfold tailWord_1902431
  simp only [CollatzResearch.WordTrace]
  refine ⟨69387358970824871192555147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46258239313883247461703431 69387358970824871192555147)
  ·
    refine ⟨104081038456237306788832721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69387358970824871192555147 104081038456237306788832721)
    ·
      refine ⟨78060778842177980091624541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104081038456237306788832721 78060778842177980091624541)
      ·
        refine ⟨29272792065816742534359203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78060778842177980091624541 29272792065816742534359203)
        ·
          refine ⟨43909188098725113801538805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29272792065816742534359203 43909188098725113801538805)
          ·
            refine ⟨4116486384255479418894263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43909188098725113801538805 4116486384255479418894263)
            ·
              refine ⟨6174729576383219128341395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116486384255479418894263 6174729576383219128341395)
              ·
                refine ⟨9262094364574828692512093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174729576383219128341395 9262094364574828692512093)
                ·
                  refine ⟨3473285386715560759692035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9262094364574828692512093 3473285386715560759692035)
                  ·
                    refine ⟨5209928080073341139538053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473285386715560759692035 5209928080073341139538053)
                    ·
                      refine ⟨976861515013751463663385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5209928080073341139538053 976861515013751463663385)
                      ·
                        rfl

theorem cell23_1902431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1902431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902431 prefixEnd_1902431 := by exact prefixLift 1902431
  have htrace : WordTrace (prefixWord ++ tailWord_1902431) baseStart_1902431 baseEnd_1902431 := by
    simpa [prefixWord, tailWord_1902431, baseEnd_1902431] using wordTrace_append hprefix tailTrace_1902431
  have hstable : (prefixWord ++ tailWord_1902431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902431).length < 2 ^ (prefixWord ++ tailWord_1902431).sum := by decide
  have hdescent : baseEnd_1902431 < baseStart_1902431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902435 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1902435 : Nat := 118140960795 + 1902435 * 2 ^ 59
def prefixEnd_1902435 : Nat := 4983230072969 + 3 ^ 40 * 1902435 * 2
def baseEnd_1902435 : Nat := 976863568936369448013367

theorem tailTrace_1902435 : CollatzResearch.WordTrace tailWord_1902435 prefixEnd_1902435 976863568936369448013367 := by
  unfold tailWord_1902435
  simp only [CollatzResearch.WordTrace]
  refine ⟨69387504862810379875700759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46258336575206919917133839 69387504862810379875700759)
  ·
    refine ⟨104081257294215569813551139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69387504862810379875700759 104081257294215569813551139)
    ·
      refine ⟨156121885941323354720326709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104081257294215569813551139 156121885941323354720326709)
      ·
        refine ⟨14636426806999064505030629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156121885941323354720326709 14636426806999064505030629)
        ·
          refine ⟨2744330026312324594693243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14636426806999064505030629 2744330026312324594693243)
          ·
            refine ⟨4116495039468486892039865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744330026312324594693243 4116495039468486892039865)
            ·
              refine ⟨3087371279601365169029899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4116495039468486892039865 3087371279601365169029899)
              ·
                refine ⟨4631056919402047753544849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087371279601365169029899 4631056919402047753544849)
                ·
                  refine ⟨3473292689551535815158637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631056919402047753544849 3473292689551535815158637)
                  ·
                    refine ⟨1302484758581825930684489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473292689551535815158637 1302484758581825930684489)
                    ·
                      refine ⟨976863568936369448013367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302484758581825930684489 976863568936369448013367)
                      ·
                        rfl

theorem cell23_1902435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1902435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902435 prefixEnd_1902435 := by exact prefixLift 1902435
  have htrace : WordTrace (prefixWord ++ tailWord_1902435) baseStart_1902435 baseEnd_1902435 := by
    simpa [prefixWord, tailWord_1902435, baseEnd_1902435] using wordTrace_append hprefix tailTrace_1902435
  have hstable : (prefixWord ++ tailWord_1902435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902435).length < 2 ^ (prefixWord ++ tailWord_1902435).sum := by decide
  have hdescent : baseEnd_1902435 < baseStart_1902435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902481 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_1902481 : Nat := 118140960795 + 1902481 * 2 ^ 59
def prefixEnd_1902481 : Nat := 4983230072969 + 3 ^ 40 * 1902481 * 2
def baseEnd_1902481 : Nat := 976887189046476268038155

theorem tailTrace_1902481 : CollatzResearch.WordTrace tailWord_1902481 prefixEnd_1902481 976887189046476268038155 := by
  unfold tailWord_1902481
  simp only [CollatzResearch.WordTrace]
  refine ⟨69389182620643729731875297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46259455080429153154583531 69389182620643729731875297)
  ·
    refine ⟨52041886965482797298906473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69389182620643729731875297 52041886965482797298906473)
    ·
      refine ⟨39031415224112097974179855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52041886965482797298906473 39031415224112097974179855)
      ·
        refine ⟨58547122836168146961269783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39031415224112097974179855 58547122836168146961269783)
        ·
          refine ⟨87820684254252220441904675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58547122836168146961269783 87820684254252220441904675)
          ·
            refine ⟨131731026381378330662857013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87820684254252220441904675 131731026381378330662857013)
            ·
              refine ⟨12349783723254218499642845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131731026381378330662857013 12349783723254218499642845)
              ·
                refine ⟨4631168896220331937366067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12349783723254218499642845 4631168896220331937366067)
                ·
                  refine ⟨6946753344330497906049101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631168896220331937366067 6946753344330497906049101)
                  ·
                    refine ⟨2605032504123936714768413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6946753344330497906049101 2605032504123936714768413)
                    ·
                      refine ⟨976887189046476268038155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605032504123936714768413 976887189046476268038155)
                      ·
                        rfl

theorem cell23_1902481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_1902481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902481 prefixEnd_1902481 := by exact prefixLift 1902481
  have htrace : WordTrace (prefixWord ++ tailWord_1902481) baseStart_1902481 baseEnd_1902481 := by
    simpa [prefixWord, tailWord_1902481, baseEnd_1902481] using wordTrace_append hprefix tailTrace_1902481
  have hstable : (prefixWord ++ tailWord_1902481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902481).length < 2 ^ (prefixWord ++ tailWord_1902481).sum := by decide
  have hdescent : baseEnd_1902481 < baseStart_1902481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902482 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1902482 : Nat := 118140960795 + 1902482 * 2 ^ 59
def prefixEnd_1902482 : Nat := 4983230072969 + 3 ^ 40 * 1902482 * 2
def baseEnd_1902482 : Nat := 976887702527130764125651

theorem tailTrace_1902482 : CollatzResearch.WordTrace tailWord_1902482 prefixEnd_1902482 976887702527130764125651 := by
  unfold tailWord_1902482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17347304773410026725665425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46259479395760071268441133 17347304773410026725665425)
  ·
    refine ⟨13010478580057520044249069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17347304773410026725665425 13010478580057520044249069)
    ·
      refine ⟨4878929467521570016593401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13010478580057520044249069 4878929467521570016593401)
      ·
        refine ⟨3659197100641177512445051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4878929467521570016593401 3659197100641177512445051)
        ·
          refine ⟨5488795650961766268667577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659197100641177512445051 5488795650961766268667577)
          ·
            refine ⟨4116596738221324701500683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5488795650961766268667577 4116596738221324701500683)
            ·
              refine ⟨6174895107331987052251025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116596738221324701500683 6174895107331987052251025)
              ·
                refine ⟨4631171330498990289188269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174895107331987052251025 4631171330498990289188269)
                ·
                  refine ⟨1736689248937121358445601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4631171330498990289188269 1736689248937121358445601)
                  ·
                    refine ⟨1302516936702841018834201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1736689248937121358445601 1302516936702841018834201)
                    ·
                      refine ⟨976887702527130764125651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302516936702841018834201 976887702527130764125651)
                      ·
                        rfl

theorem cell23_1902482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1902482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902482 prefixEnd_1902482 := by exact prefixLift 1902482
  have htrace : WordTrace (prefixWord ++ tailWord_1902482) baseStart_1902482 baseEnd_1902482 := by
    simpa [prefixWord, tailWord_1902482, baseEnd_1902482] using wordTrace_append hprefix tailTrace_1902482
  have hstable : (prefixWord ++ tailWord_1902482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902482).length < 2 ^ (prefixWord ++ tailWord_1902482).sum := by decide
  have hdescent : baseEnd_1902482 < baseStart_1902482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902486 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1902486 : Nat := 118140960795 + 1902486 * 2 ^ 59
def prefixEnd_1902486 : Nat := 4983230072969 + 3 ^ 40 * 1902486 * 2
def baseEnd_1902486 : Nat := 976889756449748748475633

theorem tailTrace_1902486 : CollatzResearch.WordTrace tailWord_1902486 prefixEnd_1902486 976889756449748748475633 := by
  unfold tailWord_1902486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336835311601600974112957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46259576657083743723871541 4336835311601600974112957)
  ·
    refine ⟨1626313241850600365292359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4336835311601600974112957 1626313241850600365292359)
    ·
      refine ⟨2439469862775900547938539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626313241850600365292359 2439469862775900547938539)
      ·
        refine ⟨3659204794163850821907809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439469862775900547938539 3659204794163850821907809)
        ·
          refine ⟨2744403595622888116430857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659204794163850821907809 2744403595622888116430857)
          ·
            refine ⟨2058302696717166087323143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744403595622888116430857 2058302696717166087323143)
            ·
              refine ⟨3087454045075749130984715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058302696717166087323143 3087454045075749130984715)
              ·
                refine ⟨4631181067613623696477073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087454045075749130984715 4631181067613623696477073)
                ·
                  refine ⟨3473385800710217772357805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4631181067613623696477073 3473385800710217772357805)
                  ·
                    refine ⟨1302519675266331664634177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3473385800710217772357805 1302519675266331664634177)
                    ·
                      refine ⟨976889756449748748475633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302519675266331664634177 976889756449748748475633)
                      ·
                        rfl

theorem cell23_1902486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1902486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902486 prefixEnd_1902486 := by exact prefixLift 1902486
  have htrace : WordTrace (prefixWord ++ tailWord_1902486) baseStart_1902486 baseEnd_1902486 := by
    simpa [prefixWord, tailWord_1902486, baseEnd_1902486] using wordTrace_append hprefix tailTrace_1902486
  have hstable : (prefixWord ++ tailWord_1902486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902486).length < 2 ^ (prefixWord ++ tailWord_1902486).sum := by decide
  have hdescent : baseEnd_1902486 < baseStart_1902486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902571 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3]
def baseStart_1902571 : Nat := 118140960795 + 1902571 * 2 ^ 59
def prefixEnd_1902571 : Nat := 4983230072969 + 3 ^ 40 * 1902571 * 2
def baseEnd_1902571 : Nat := 976933402305380915912741

theorem tailTrace_1902571 : CollatzResearch.WordTrace tailWord_1902571 prefixEnd_1902571 976933402305380915912741 := by
  unfold tailWord_1902571
  simp only [CollatzResearch.WordTrace]
  refine ⟨69392465190317675102651567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46261643460211783401767711 69392465190317675102651567)
  ·
    refine ⟨104088697785476512653977351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69392465190317675102651567 104088697785476512653977351)
    ·
      refine ⟨156133046678214768980966027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104088697785476512653977351 156133046678214768980966027)
      ·
        refine ⟨234199570017322153471449041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156133046678214768980966027 234199570017322153471449041)
        ·
          refine ⟨175649677512991615103586781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234199570017322153471449041 175649677512991615103586781)
          ·
            refine ⟨65868629067371855663845043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175649677512991615103586781 65868629067371855663845043)
            ·
              refine ⟨98802943601057783495767565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65868629067371855663845043 98802943601057783495767565)
              ·
                refine ⟨37051103850396668810912837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98802943601057783495767565 37051103850396668810912837)
                ·
                  refine ⟨6947081971949375402046157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37051103850396668810912837 6947081971949375402046157)
                  ·
                    refine ⟨2605155739481015775767309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6947081971949375402046157 2605155739481015775767309)
                    ·
                      refine ⟨976933402305380915912741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605155739481015775767309 976933402305380915912741)
                      ·
                        rfl

theorem cell23_1902571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3].length) (baseStart_1902571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902571 prefixEnd_1902571 := by exact prefixLift 1902571
  have htrace : WordTrace (prefixWord ++ tailWord_1902571) baseStart_1902571 baseEnd_1902571 := by
    simpa [prefixWord, tailWord_1902571, baseEnd_1902571] using wordTrace_append hprefix tailTrace_1902571
  have hstable : (prefixWord ++ tailWord_1902571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902571).length < 2 ^ (prefixWord ++ tailWord_1902571).sum := by decide
  have hdescent : baseEnd_1902571 < baseStart_1902571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902611 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_1902611 : Nat := 118140960795 + 1902611 * 2 ^ 59
def prefixEnd_1902611 : Nat := 4983230072969 + 3 ^ 40 * 1902611 * 2
def baseEnd_1902611 : Nat := 976953941531560759412557

theorem tailTrace_1902611 : CollatzResearch.WordTrace tailWord_1902611 prefixEnd_1902611 976953941531560759412557 := by
  unfold tailWord_1902611
  simp only [CollatzResearch.WordTrace]
  refine ⟨69393924110172761934107687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46262616073448507956071791 69393924110172761934107687)
  ·
    refine ⟨104090886165259142901161531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69393924110172761934107687 104090886165259142901161531)
    ·
      refine ⟨156136329247888714351742297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104090886165259142901161531 156136329247888714351742297)
      ·
        refine ⟨117102246935916535763806723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156136329247888714351742297 117102246935916535763806723)
        ·
          refine ⟨175653370403874803645710085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117102246935916535763806723 175653370403874803645710085)
          ·
            refine ⟨32935006950726525683570641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175653370403874803645710085 32935006950726525683570641)
            ·
              refine ⟨24701255213044894262677981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32935006950726525683570641 24701255213044894262677981)
              ·
                refine ⟨9262970704891835348504243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24701255213044894262677981 9262970704891835348504243)
                ·
                  refine ⟨13894456057337753022756365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9262970704891835348504243 13894456057337753022756365)
                  ·
                    refine ⟨5210421021501657383533637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13894456057337753022756365 5210421021501657383533637)
                    ·
                      refine ⟨976953941531560759412557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5210421021501657383533637 976953941531560759412557)
                      ·
                        rfl

theorem cell23_1902611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_1902611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902611 prefixEnd_1902611 := by exact prefixLift 1902611
  have htrace : WordTrace (prefixWord ++ tailWord_1902611) baseStart_1902611 baseEnd_1902611 := by
    simpa [prefixWord, tailWord_1902611, baseEnd_1902611] using wordTrace_append hprefix tailTrace_1902611
  have hstable : (prefixWord ++ tailWord_1902611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902611).length < 2 ^ (prefixWord ++ tailWord_1902611).sum := by decide
  have hdescent : baseEnd_1902611 < baseStart_1902611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902662 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1902662 : Nat := 118140960795 + 1902662 * 2 ^ 59
def prefixEnd_1902662 : Nat := 4983230072969 + 3 ^ 40 * 1902662 * 2
def baseEnd_1902662 : Nat := 976980129044940059874823

theorem tailTrace_1902662 : CollatzResearch.WordTrace tailWord_1902662 prefixEnd_1902662 976980129044940059874823 := by
  unfold tailWord_1902662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168618257280874926381695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46263856155325331762809493 2168618257280874926381695)
  ·
    refine ⟨3252927385921312389572543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168618257280874926381695 3252927385921312389572543)
    ·
      refine ⟨4879391078881968584358815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3252927385921312389572543 4879391078881968584358815)
      ·
        refine ⟨7319086618322952876538223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879391078881968584358815 7319086618322952876538223)
        ·
          refine ⟨10978629927484429314807335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319086618322952876538223 10978629927484429314807335)
          ·
            refine ⟨16467944891226643972211003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978629927484429314807335 16467944891226643972211003)
            ·
              refine ⟨24701917336839965958316505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16467944891226643972211003 24701917336839965958316505)
              ·
                refine ⟨18526438002629974468737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24701917336839965958316505 18526438002629974468737379)
                ·
                  refine ⟨27789657003944961703106069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18526438002629974468737379 27789657003944961703106069)
                  ·
                    refine ⟨1302640172059920079833097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27789657003944961703106069 1302640172059920079833097)
                    ·
                      refine ⟨976980129044940059874823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302640172059920079833097 976980129044940059874823)
                      ·
                        rfl

theorem cell23_1902662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1902662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902662 prefixEnd_1902662 := by exact prefixLift 1902662
  have htrace : WordTrace (prefixWord ++ tailWord_1902662) baseStart_1902662 baseEnd_1902662 := by
    simpa [prefixWord, tailWord_1902662, baseEnd_1902662] using wordTrace_append hprefix tailTrace_1902662
  have hstable : (prefixWord ++ tailWord_1902662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902662).length < 2 ^ (prefixWord ++ tailWord_1902662).sum := by decide
  have hdescent : baseEnd_1902662 < baseStart_1902662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902685 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 8]
def baseStart_1902685 : Nat := 118140960795 + 1902685 * 2 ^ 59
def prefixEnd_1902685 : Nat := 4983230072969 + 3 ^ 40 * 1902685 * 2
def baseEnd_1902685 : Nat := 108554659899999274431913

theorem tailTrace_1902685 : CollatzResearch.WordTrace tailWord_1902685 prefixEnd_1902685 108554659899999274431913 := by
  unfold tailWord_1902685
  simp only [CollatzResearch.WordTrace]
  refine ⟨69396623111904672572301509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46264415407936448381534339 69396623111904672572301509)
  ·
    refine ⟨13011866833482126107306533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69396623111904672572301509 13011866833482126107306533)
    ·
      refine ⟨2439725031277898645119975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13011866833482126107306533 2439725031277898645119975)
      ·
        refine ⟨3659587546916847967679963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439725031277898645119975 3659587546916847967679963)
        ·
          refine ⟨5489381320375271951519945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3659587546916847967679963 5489381320375271951519945)
          ·
            refine ⟨4117035990281453963639959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5489381320375271951519945 4117035990281453963639959)
            ·
              refine ⟨6175553985422180945459939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117035990281453963639959 6175553985422180945459939)
              ·
                refine ⟨9263330978133271418189909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175553985422180945459939 9263330978133271418189909)
                ·
                  refine ⟨108554659899999274431913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9263330978133271418189909 108554659899999274431913)
                  ·
                    rfl

theorem cell23_1902685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_1902685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902685 prefixEnd_1902685 := by exact prefixLift 1902685
  have htrace : WordTrace (prefixWord ++ tailWord_1902685) baseStart_1902685 baseEnd_1902685 := by
    simpa [prefixWord, tailWord_1902685, baseEnd_1902685] using wordTrace_append hprefix tailTrace_1902685
  have hstable : (prefixWord ++ tailWord_1902685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902685).length < 2 ^ (prefixWord ++ tailWord_1902685).sum := by decide
  have hdescent : baseEnd_1902685 < baseStart_1902685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902746 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1902746 : Nat := 118140960795 + 1902746 * 2 ^ 59
def prefixEnd_1902746 : Nat := 4983230072969 + 3 ^ 40 * 1902746 * 2
def baseEnd_1902746 : Nat := 977023261419917731224437

theorem tailTrace_1902746 : CollatzResearch.WordTrace tailWord_1902746 prefixEnd_1902746 977023261419917731224437 := by
  unfold tailWord_1902746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17349711991170919997568023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46265898643122453326848061 17349711991170919997568023)
  ·
    refine ⟨26024567986756379996352035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17349711991170919997568023 26024567986756379996352035)
    ·
      refine ⟨39036851980134569994528053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26024567986756379996352035 39036851980134569994528053)
      ·
        refine ⟨3659704873137615936987005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39036851980134569994528053 3659704873137615936987005)
        ·
          refine ⟨1372389327426605976370127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3659704873137615936987005 1372389327426605976370127)
          ·
            refine ⟨2058583991139908964555191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372389327426605976370127 2058583991139908964555191)
            ·
              refine ⟨3087875986709863446832787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058583991139908964555191 3087875986709863446832787)
              ·
                refine ⟨4631813980064795170249181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087875986709863446832787 4631813980064795170249181)
                ·
                  refine ⟨1736930242524298188843443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4631813980064795170249181 1736930242524298188843443)
                  ·
                    refine ⟨2605395363786447283265165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1736930242524298188843443 2605395363786447283265165)
                    ·
                      refine ⟨977023261419917731224437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605395363786447283265165 977023261419917731224437)
                      ·
                        rfl

theorem cell23_1902746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1902746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902746 prefixEnd_1902746 := by exact prefixLift 1902746
  have htrace : WordTrace (prefixWord ++ tailWord_1902746) baseStart_1902746 baseEnd_1902746 := by
    simpa [prefixWord, tailWord_1902746, baseEnd_1902746] using wordTrace_append hprefix tailTrace_1902746
  have hstable : (prefixWord ++ tailWord_1902746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902746).length < 2 ^ (prefixWord ++ tailWord_1902746).sum := by decide
  have hdescent : baseEnd_1902746 < baseStart_1902746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902748 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1902748 : Nat := 118140960795 + 1902748 * 2 ^ 59
def prefixEnd_1902748 : Nat := 4983230072969 + 3 ^ 40 * 1902748 * 2
def baseEnd_1902748 : Nat := 977024288381226723399427

theorem tailTrace_1902748 : CollatzResearch.WordTrace tailWord_1902748 prefixEnd_1902748 977024288381226723399427 := by
  unfold tailWord_1902748
  simp only [CollatzResearch.WordTrace]
  refine ⟨34699460455338217165922449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46265947273784289554563265 34699460455338217165922449)
  ·
    refine ⟨26024595341503662874441837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34699460455338217165922449 26024595341503662874441837)
    ·
      refine ⟨9759223253063873577915689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26024595341503662874441837 9759223253063873577915689)
      ·
        refine ⟨7319417439797905183436767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9759223253063873577915689 7319417439797905183436767)
        ·
          refine ⟨10979126159696857775155151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319417439797905183436767 10979126159696857775155151)
          ·
            refine ⟨16468689239545286662732727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979126159696857775155151 16468689239545286662732727)
            ·
              refine ⟨24703033859317929994099091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468689239545286662732727 24703033859317929994099091)
              ·
                refine ⟨37054550788976894991148637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24703033859317929994099091 37054550788976894991148637)
                ·
                  refine ⟨13895456545866335621680739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37054550788976894991148637 13895456545866335621680739)
                  ·
                    refine ⟨20843184818799503432521109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13895456545866335621680739 20843184818799503432521109)
                    ·
                      refine ⟨977024288381226723399427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20843184818799503432521109 977024288381226723399427)
                      ·
                        rfl

theorem cell23_1902748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1902748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902748 prefixEnd_1902748 := by exact prefixLift 1902748
  have htrace : WordTrace (prefixWord ++ tailWord_1902748) baseStart_1902748 baseEnd_1902748 := by
    simpa [prefixWord, tailWord_1902748, baseEnd_1902748] using wordTrace_append hprefix tailTrace_1902748
  have hstable : (prefixWord ++ tailWord_1902748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902748).length < 2 ^ (prefixWord ++ tailWord_1902748).sum := by decide
  have hdescent : baseEnd_1902748 < baseStart_1902748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902765 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1902765 : Nat := 118140960795 + 1902765 * 2 ^ 59
def prefixEnd_1902765 : Nat := 4983230072969 + 3 ^ 40 * 1902765 * 2
def baseEnd_1902765 : Nat := 977033017552353156886849

theorem tailTrace_1902765 : CollatzResearch.WordTrace tailWord_1902765 prefixEnd_1902765 977033017552353156886849 := by
  unfold tailWord_1902765
  simp only [CollatzResearch.WordTrace]
  refine ⟨69399540951614846235213749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46266360634409897490142499 69399540951614846235213749)
  ·
    refine ⟨6506206964213891834551289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69399540951614846235213749 6506206964213891834551289)
    ·
      refine ⟨4879655223160418875913467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6506206964213891834551289 4879655223160418875913467)
      ·
        refine ⟨7319482834740628313870201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879655223160418875913467 7319482834740628313870201)
        ·
          refine ⟨5489612126055471235402651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7319482834740628313870201 5489612126055471235402651)
          ·
            refine ⟨8234418189083206853103977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489612126055471235402651 8234418189083206853103977)
            ·
              refine ⟨6175813641812405139827983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234418189083206853103977 6175813641812405139827983)
              ·
                refine ⟨9263720462718607709741975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175813641812405139827983 9263720462718607709741975)
                ·
                  refine ⟨13895580694077911564612963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263720462718607709741975 13895580694077911564612963)
                  ·
                    refine ⟨20843371041116867346919445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13895580694077911564612963 20843371041116867346919445)
                    ·
                      refine ⟨977033017552353156886849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20843371041116867346919445 977033017552353156886849)
                      ·
                        rfl

theorem cell23_1902765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1902765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902765 prefixEnd_1902765 := by exact prefixLift 1902765
  have htrace : WordTrace (prefixWord ++ tailWord_1902765) baseStart_1902765 baseEnd_1902765 := by
    simpa [prefixWord, tailWord_1902765, baseEnd_1902765] using wordTrace_append hprefix tailTrace_1902765
  have hstable : (prefixWord ++ tailWord_1902765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902765).length < 2 ^ (prefixWord ++ tailWord_1902765).sum := by decide
  have hdescent : baseEnd_1902765 < baseStart_1902765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902766 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1902766 : Nat := 118140960795 + 1902766 * 2 ^ 59
def prefixEnd_1902766 : Nat := 4983230072969 + 3 ^ 40 * 1902766 * 2
def baseEnd_1902766 : Nat := 325677843677669217658115

theorem tailTrace_1902766 : CollatzResearch.WordTrace tailWord_1902766 prefixEnd_1902766 325677843677669217658115 := by
  unfold tailWord_1902766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674947178076402925750019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46266384949740815604000101 8674947178076402925750019)
  ·
    refine ⟨13012420767114604388625029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674947178076402925750019 13012420767114604388625029)
    ·
      refine ⟨2439828893833988322867193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13012420767114604388625029 2439828893833988322867193)
      ·
        refine ⟨1829871670375491242150395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439828893833988322867193 1829871670375491242150395)
        ·
          refine ⟨2744807505563236863225593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829871670375491242150395 2744807505563236863225593)
          ·
            refine ⟨2058605629172427647419195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744807505563236863225593 2058605629172427647419195)
            ·
              refine ⟨3087908443758641471128793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058605629172427647419195 3087908443758641471128793)
              ·
                refine ⟨2315931332818981103346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087908443758641471128793 2315931332818981103346595)
                ·
                  refine ⟨3473896999228471655019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315931332818981103346595 3473896999228471655019893)
                  ·
                    refine ⟨325677843677669217658115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3473896999228471655019893 325677843677669217658115)
                    ·
                      rfl

theorem cell23_1902766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1902766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902766 prefixEnd_1902766 := by exact prefixLift 1902766
  have htrace : WordTrace (prefixWord ++ tailWord_1902766) baseStart_1902766 baseEnd_1902766 := by
    simpa [prefixWord, tailWord_1902766, baseEnd_1902766] using wordTrace_append hprefix tailTrace_1902766
  have hstable : (prefixWord ++ tailWord_1902766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902766).length < 2 ^ (prefixWord ++ tailWord_1902766).sum := by decide
  have hdescent : baseEnd_1902766 < baseStart_1902766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902769 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1902769 : Nat := 118140960795 + 1902769 * 2 ^ 59
def prefixEnd_1902769 : Nat := 4983230072969 + 3 ^ 40 * 1902769 * 2
def baseEnd_1902769 : Nat := 977035071474971141236831

theorem tailTrace_1902769 : CollatzResearch.WordTrace tailWord_1902769 prefixEnd_1902769 977035071474971141236831 := by
  unfold tailWord_1902769
  simp only [CollatzResearch.WordTrace]
  refine ⟨69399686843600354918359361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46266457895733569945572907 69399686843600354918359361)
  ·
    refine ⟨52049765132700266188769521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69399686843600354918359361 52049765132700266188769521)
    ·
      refine ⟨39037323849525199641577141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52049765132700266188769521 39037323849525199641577141)
      ·
        refine ⟨3659749110892987466397857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39037323849525199641577141 3659749110892987466397857)
        ·
          refine ⟨2744811833169740599798393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659749110892987466397857 2744811833169740599798393)
          ·
            refine ⟨2058608874877305449848795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744811833169740599798393 2058608874877305449848795)
            ·
              refine ⟨3087913312315958174773193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058608874877305449848795 3087913312315958174773193)
              ·
                refine ⟨2315934984236968631079895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3087913312315958174773193 2315934984236968631079895)
                ·
                  refine ⟨3473902476355452946619843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315934984236968631079895 3473902476355452946619843)
                  ·
                    refine ⟨5210853714533179419929765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3473902476355452946619843 5210853714533179419929765)
                    ·
                      refine ⟨977035071474971141236831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5210853714533179419929765 977035071474971141236831)
                      ·
                        rfl

theorem cell23_1902769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1902769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902769 prefixEnd_1902769 := by exact prefixLift 1902769
  have htrace : WordTrace (prefixWord ++ tailWord_1902769) baseStart_1902769 baseEnd_1902769 := by
    simpa [prefixWord, tailWord_1902769, baseEnd_1902769] using wordTrace_append hprefix tailTrace_1902769
  have hstable : (prefixWord ++ tailWord_1902769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902769).length < 2 ^ (prefixWord ++ tailWord_1902769).sum := by decide
  have hdescent : baseEnd_1902769 < baseStart_1902769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902782 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1902782 : Nat := 118140960795 + 1902782 * 2 ^ 59
def prefixEnd_1902782 : Nat := 4983230072969 + 3 ^ 40 * 1902782 * 2
def baseEnd_1902782 : Nat := 977041746723479590374271

theorem tailTrace_1902782 : CollatzResearch.WordTrace tailWord_1902782 prefixEnd_1902782 977041746723479590374271 := by
  unfold tailWord_1902782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8675020124069157267322825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46266773995035505425721733 8675020124069157267322825)
  ·
    refine ⟨6506265093051867950492119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8675020124069157267322825 6506265093051867950492119)
    ·
      refine ⟨9759397639577801925738179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6506265093051867950492119 9759397639577801925738179)
      ·
        refine ⟨14639096459366702888607269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9759397639577801925738179 14639096459366702888607269)
        ·
          refine ⟨2744830586131256791613863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14639096459366702888607269 2744830586131256791613863)
          ·
            refine ⟨4117245879196885187420795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744830586131256791613863 4117245879196885187420795)
            ·
              refine ⟨6175868818795327781131193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117245879196885187420795 6175868818795327781131193)
              ·
                refine ⟨4631901614096495835848395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6175868818795327781131193 4631901614096495835848395)
                ·
                  refine ⟨6947852421144743753772593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631901614096495835848395 6947852421144743753772593)
                  ·
                    refine ⟨5210889315858557815329445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6947852421144743753772593 5210889315858557815329445)
                    ·
                      refine ⟨977041746723479590374271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5210889315858557815329445 977041746723479590374271)
                      ·
                        rfl

theorem cell23_1902782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1902782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902782 prefixEnd_1902782 := by exact prefixLift 1902782
  have htrace : WordTrace (prefixWord ++ tailWord_1902782) baseStart_1902782 baseEnd_1902782 := by
    simpa [prefixWord, tailWord_1902782, baseEnd_1902782] using wordTrace_append hprefix tailTrace_1902782
  have hstable : (prefixWord ++ tailWord_1902782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902782).length < 2 ^ (prefixWord ++ tailWord_1902782).sum := by decide
  have hdescent : baseEnd_1902782 < baseStart_1902782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902819 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1902819 : Nat := 118140960795 + 1902819 * 2 ^ 59
def prefixEnd_1902819 : Nat := 4983230072969 + 3 ^ 40 * 1902819 * 2
def baseEnd_1902819 : Nat := 977060745507695945611601

theorem tailTrace_1902819 : CollatzResearch.WordTrace tailWord_1902819 prefixEnd_1902819 977060745507695945611601 := by
  unfold tailWord_1902819
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401510493419213457679511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46267673662279475638453007 69401510493419213457679511)
  ·
    refine ⟨104102265740128820186519267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69401510493419213457679511 104102265740128820186519267)
    ·
      refine ⟨156153398610193230279778901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104102265740128820186519267 156153398610193230279778901)
      ·
        refine ⟨1829922639963201917341159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 156153398610193230279778901 1829922639963201917341159)
        ·
          refine ⟨2744883959944802876011739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829922639963201917341159 2744883959944802876011739)
          ·
            refine ⟨4117325939917204314017609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744883959944802876011739 4117325939917204314017609)
            ·
              refine ⟨3087994454937903235513207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117325939917204314017609 3087994454937903235513207)
              ·
                refine ⟨4631991682406854853269811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3087994454937903235513207 4631991682406854853269811)
                ·
                  refine ⟨6947987523610282279904717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631991682406854853269811 6947987523610282279904717)
                  ·
                    refine ⟨2605495321353855854964269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6947987523610282279904717 2605495321353855854964269)
                    ·
                      refine ⟨977060745507695945611601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605495321353855854964269 977060745507695945611601)
                      ·
                        rfl

theorem cell23_1902819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1902819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902819 prefixEnd_1902819 := by exact prefixLift 1902819
  have htrace : WordTrace (prefixWord ++ tailWord_1902819) baseStart_1902819 baseEnd_1902819 := by
    simpa [prefixWord, tailWord_1902819, baseEnd_1902819] using wordTrace_append hprefix tailTrace_1902819
  have hstable : (prefixWord ++ tailWord_1902819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902819).length < 2 ^ (prefixWord ++ tailWord_1902819).sum := by decide
  have hdescent : baseEnd_1902819 < baseStart_1902819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902825 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 5, 4, 2]
def baseStart_1902825 : Nat := 118140960795 + 1902825 * 2 ^ 59
def prefixEnd_1902825 : Nat := 4983230072969 + 3 ^ 40 * 1902825 * 2
def baseEnd_1902825 : Nat := 977063826391622922136573

theorem tailTrace_1902825 : CollatzResearch.WordTrace tailWord_1902825 prefixEnd_1902825 977063826391622922136573 := by
  unfold tailWord_1902825
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401729331397476482397929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46267819554264984321598619 69401729331397476482397929)
  ·
    refine ⟨52051296998548107361798447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69401729331397476482397929 52051296998548107361798447)
    ·
      refine ⟨78076945497822161042697671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52051296998548107361798447 78076945497822161042697671)
      ·
        refine ⟨117115418246733241564046507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78076945497822161042697671 117115418246733241564046507)
        ·
          refine ⟨175673127370099862346069761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117115418246733241564046507 175673127370099862346069761)
          ·
            refine ⟨131754845527574896759552321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175673127370099862346069761 131754845527574896759552321)
            ·
              refine ⟨98816134145681172569664241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131754845527574896759552321 98816134145681172569664241)
              ·
                refine ⟨74112100609260879427248181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98816134145681172569664241 74112100609260879427248181)
                ·
                  refine ⟨6948009432118207446304517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74112100609260879427248181 6948009432118207446304517)
                  ·
                    refine ⟨1302751768522163896182097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948009432118207446304517 1302751768522163896182097)
                    ·
                      refine ⟨977063826391622922136573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302751768522163896182097 977063826391622922136573)
                      ·
                        rfl

theorem cell23_1902825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4, 2].length) (baseStart_1902825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902825 prefixEnd_1902825 := by exact prefixLift 1902825
  have htrace : WordTrace (prefixWord ++ tailWord_1902825) baseStart_1902825 baseEnd_1902825 := by
    simpa [prefixWord, tailWord_1902825, baseEnd_1902825] using wordTrace_append hprefix tailTrace_1902825
  have hstable : (prefixWord ++ tailWord_1902825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902825).length < 2 ^ (prefixWord ++ tailWord_1902825).sum := by decide
  have hdescent : baseEnd_1902825 < baseStart_1902825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902842 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_1902842 : Nat := 118140960795 + 1902842 * 2 ^ 59
def prefixEnd_1902842 : Nat := 4983230072969 + 3 ^ 40 * 1902842 * 2
def baseEnd_1902842 : Nat := 977072555562749355623995

theorem tailTrace_1902842 : CollatzResearch.WordTrace tailWord_1902842 prefixEnd_1902842 977072555562749355623995 := by
  unfold tailWord_1902842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350587343083972096441695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46268232914890592257177853 17350587343083972096441695)
  ·
    refine ⟨26025881014625958144662543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17350587343083972096441695 26025881014625958144662543)
    ·
      refine ⟨39038821521938937216993815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26025881014625958144662543 39038821521938937216993815)
      ·
        refine ⟨58558232282908405825490723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39038821521938937216993815 58558232282908405825490723)
        ·
          refine ⟨87837348424362608738236085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58558232282908405825490723 87837348424362608738236085)
          ·
            refine ⟨8234751414783994569209633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87837348424362608738236085 8234751414783994569209633)
            ·
              refine ⟨6176063561087995926907225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234751414783994569209633 6176063561087995926907225)
              ·
                refine ⟨4632047670815996945180419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6176063561087995926907225 4632047670815996945180419)
                ·
                  refine ⟨6948071506223995417770629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632047670815996945180419 6948071506223995417770629)
                  ·
                    refine ⟨1302763407416999140831993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948071506223995417770629 1302763407416999140831993)
                    ·
                      refine ⟨977072555562749355623995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302763407416999140831993 977072555562749355623995)
                      ·
                        rfl

theorem cell23_1902842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_1902842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902842 prefixEnd_1902842 := by exact prefixLift 1902842
  have htrace : WordTrace (prefixWord ++ tailWord_1902842) baseStart_1902842 baseEnd_1902842 := by
    simpa [prefixWord, tailWord_1902842, baseEnd_1902842] using wordTrace_append hprefix tailTrace_1902842
  have hstable : (prefixWord ++ tailWord_1902842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902842).length < 2 ^ (prefixWord ++ tailWord_1902842).sum := by decide
  have hdescent : baseEnd_1902842 < baseStart_1902842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902865 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 7]
def baseStart_1902865 : Nat := 118140960795 + 1902865 * 2 ^ 59
def prefixEnd_1902865 : Nat := 4983230072969 + 3 ^ 40 * 1902865 * 2
def baseEnd_1902865 : Nat := 108564929513089196181821

theorem tailTrace_1902865 : CollatzResearch.WordTrace tailWord_1902865 prefixEnd_1902865 108564929513089196181821 := by
  unfold tailWord_1902865
  simp only [CollatzResearch.WordTrace]
  refine ⟨69403188251252563313854049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46268792167501708875902699 69403188251252563313854049)
  ·
    refine ⟨52052391188439422485390537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69403188251252563313854049 52052391188439422485390537)
    ·
      refine ⟨39039293391329566864042903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52052391188439422485390537 39039293391329566864042903)
      ·
        refine ⟨58558940086994350296064355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39039293391329566864042903 58558940086994350296064355)
        ·
          refine ⟨87838410130491525444096533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58558940086994350296064355 87838410130491525444096533)
          ·
            refine ⟨4117425474866790255192025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87838410130491525444096533 4117425474866790255192025)
            ·
              refine ⟨3088069106150092691394019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4117425474866790255192025 3088069106150092691394019)
              ·
                refine ⟨4632103659225139037091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088069106150092691394019 4632103659225139037091029)
                ·
                  refine ⟨108564929513089196181821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4632103659225139037091029 108564929513089196181821)
                  ·
                    rfl

theorem cell23_1902865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_1902865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902865 prefixEnd_1902865 := by exact prefixLift 1902865
  have htrace : WordTrace (prefixWord ++ tailWord_1902865) baseStart_1902865 baseEnd_1902865 := by
    simpa [prefixWord, tailWord_1902865, baseEnd_1902865] using wordTrace_append hprefix tailTrace_1902865
  have hstable : (prefixWord ++ tailWord_1902865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902865).length < 2 ^ (prefixWord ++ tailWord_1902865).sum := by decide
  have hdescent : baseEnd_1902865 < baseStart_1902865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902875 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3]
def baseStart_1902875 : Nat := 118140960795 + 1902875 * 2 ^ 59
def prefixEnd_1902875 : Nat := 4983230072969 + 3 ^ 40 * 1902875 * 2
def baseEnd_1902875 : Nat := 977089500424347726511343

theorem tailTrace_1902875 : CollatzResearch.WordTrace tailWord_1902875 prefixEnd_1902875 977089500424347726511343 := by
  unfold tailWord_1902875
  simp only [CollatzResearch.WordTrace]
  refine ⟨69403552981216335021718079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46269035320810890014478719 69403552981216335021718079)
  ·
    refine ⟨104105329471824502532577119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69403552981216335021718079 104105329471824502532577119)
    ·
      refine ⟨156157994207736753798865679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104105329471824502532577119 156157994207736753798865679)
      ·
        refine ⟨234236991311605130698298519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156157994207736753798865679 234236991311605130698298519)
        ·
          refine ⟨351355486967407696047447779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234236991311605130698298519 351355486967407696047447779)
          ·
            refine ⟨527033230451111544071171669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351355486967407696047447779 527033230451111544071171669)
            ·
              refine ⟨6176170669348963407084043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 527033230451111544071171669 6176170669348963407084043)
              ·
                refine ⟨9264256004023445110626065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176170669348963407084043 9264256004023445110626065)
                ·
                  refine ⟨6948192003017583832969549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264256004023445110626065 6948192003017583832969549)
                  ·
                    refine ⟨2605572001131593937363581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6948192003017583832969549 2605572001131593937363581)
                    ·
                      refine ⟨977089500424347726511343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605572001131593937363581 977089500424347726511343)
                      ·
                        rfl

theorem cell23_1902875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3].length) (baseStart_1902875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902875 prefixEnd_1902875 := by exact prefixLift 1902875
  have htrace : WordTrace (prefixWord ++ tailWord_1902875) baseStart_1902875 baseEnd_1902875 := by
    simpa [prefixWord, tailWord_1902875, baseEnd_1902875] using wordTrace_append hprefix tailTrace_1902875
  have hstable : (prefixWord ++ tailWord_1902875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902875).length < 2 ^ (prefixWord ++ tailWord_1902875).sum := by decide
  have hdescent : baseEnd_1902875 < baseStart_1902875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902915 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4]
def baseStart_1902915 : Nat := 118140960795 + 1902915 * 2 ^ 59
def prefixEnd_1902915 : Nat := 4983230072969 + 3 ^ 40 * 1902915 * 2
def baseEnd_1902915 : Nat := 977110039650527570011159

theorem tailTrace_1902915 : CollatzResearch.WordTrace tailWord_1902915 prefixEnd_1902915 977110039650527570011159 := by
  unfold tailWord_1902915
  simp only [CollatzResearch.WordTrace]
  refine ⟨69405011901071421853174199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46270007934047614568782799 69405011901071421853174199)
  ·
    refine ⟨104107517851607132779761299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69405011901071421853174199 104107517851607132779761299)
    ·
      refine ⟨156161276777410699169641949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104107517851607132779761299 156161276777410699169641949)
      ·
        refine ⟨58560478791529012188615731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156161276777410699169641949 58560478791529012188615731)
        ·
          refine ⟨87840718187293518282923597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58560478791529012188615731 87840718187293518282923597)
          ·
            refine ⟨32940269320235069356096349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87840718187293518282923597 32940269320235069356096349)
            ·
              refine ⟨12352600995088151008536131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32940269320235069356096349 12352600995088151008536131)
              ·
                refine ⟨18528901492632226512804197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12352600995088151008536131 18528901492632226512804197)
                ·
                  refine ⟨3474169029868542471150787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18528901492632226512804197 3474169029868542471150787)
                  ·
                    refine ⟨5211253544802813706726181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3474169029868542471150787 5211253544802813706726181)
                    ·
                      refine ⟨977110039650527570011159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5211253544802813706726181 977110039650527570011159)
                      ·
                        rfl

theorem cell23_1902915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_1902915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902915 prefixEnd_1902915 := by exact prefixLift 1902915
  have htrace : WordTrace (prefixWord ++ tailWord_1902915) baseStart_1902915 baseEnd_1902915 := by
    simpa [prefixWord, tailWord_1902915, baseEnd_1902915] using wordTrace_append hprefix tailTrace_1902915
  have hstable : (prefixWord ++ tailWord_1902915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902915).length < 2 ^ (prefixWord ++ tailWord_1902915).sum := by decide
  have hdescent : baseEnd_1902915 < baseStart_1902915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1902916 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 7]
def baseStart_1902916 : Nat := 118140960795 + 1902916 * 2 ^ 59
def prefixEnd_1902916 : Nat := 4983230072969 + 3 ^ 40 * 1902916 * 2
def baseEnd_1902916 : Nat := 108567839236798007344295

theorem tailTrace_1902916 : CollatzResearch.WordTrace tailWord_1902916 prefixEnd_1902916 108567839236798007344295 := by
  unfold tailWord_1902916
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702524187033899511980301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46270032249378532682640401 34702524187033899511980301)
  ·
    refine ⟨13013446570137712316992613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34702524187033899511980301 13013446570137712316992613)
    ·
      refine ⟨2440021231900821059436115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13013446570137712316992613 2440021231900821059436115)
      ·
        refine ⟨3660031847851231589154173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440021231900821059436115 3660031847851231589154173)
        ·
          refine ⟨1372511942944211845932815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3660031847851231589154173 1372511942944211845932815)
          ·
            refine ⟨2058767914416317768899223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372511942944211845932815 2058767914416317768899223)
            ·
              refine ⟨3088151871624476653348835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058767914416317768899223 3088151871624476653348835)
              ·
                refine ⟨4632227807436714980023253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088151871624476653348835 4632227807436714980023253)
                ·
                  refine ⟨108567839236798007344295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4632227807436714980023253 108567839236798007344295)
                  ·
                    rfl

theorem cell23_1902916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_1902916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1902916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1902916 prefixEnd_1902916 := by exact prefixLift 1902916
  have htrace : WordTrace (prefixWord ++ tailWord_1902916) baseStart_1902916 baseEnd_1902916 := by
    simpa [prefixWord, tailWord_1902916, baseEnd_1902916] using wordTrace_append hprefix tailTrace_1902916
  have hstable : (prefixWord ++ tailWord_1902916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1902916).length < 2 ^ (prefixWord ++ tailWord_1902916).sum := by decide
  have hdescent : baseEnd_1902916 < baseStart_1902916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1902916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903002 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_1903002 : Nat := 118140960795 + 1903002 * 2 ^ 59
def prefixEnd_1903002 : Nat := 4983230072969 + 3 ^ 40 * 1903002 * 2
def baseEnd_1903002 : Nat := 325718237489156243207753

theorem tailTrace_1903002 : CollatzResearch.WordTrace tailWord_1903002 prefixEnd_1903002 325718237489156243207753 := by
  unfold tailWord_1903002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352046262939058927897815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46272123367837490474394173 17352046262939058927897815)
  ·
    refine ⟨26028069394408588391846723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17352046262939058927897815 26028069394408588391846723)
    ·
      refine ⟨39042104091612882587770085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26028069394408588391846723 39042104091612882587770085)
      ·
        refine ⟨7320394517177415485206891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39042104091612882587770085 7320394517177415485206891)
        ·
          refine ⟨10980591775766123227810337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7320394517177415485206891 10980591775766123227810337)
          ·
            refine ⟨8235443831824592420857753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10980591775766123227810337 8235443831824592420857753)
            ·
              refine ⟨6176582873868444315643315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235443831824592420857753 6176582873868444315643315)
              ·
                refine ⟨9264874310802666473464973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176582873868444315643315 9264874310802666473464973)
                ·
                  refine ⟨3474327866550999927549365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9264874310802666473464973 3474327866550999927549365)
                  ·
                    refine ⟨325718237489156243207753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3474327866550999927549365 325718237489156243207753)
                    ·
                      rfl

theorem cell23_1903002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_1903002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903002 prefixEnd_1903002 := by exact prefixLift 1903002
  have htrace : WordTrace (prefixWord ++ tailWord_1903002) baseStart_1903002 baseEnd_1903002 := by
    simpa [prefixWord, tailWord_1903002, baseEnd_1903002] using wordTrace_append hprefix tailTrace_1903002
  have hstable : (prefixWord ++ tailWord_1903002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903002).length < 2 ^ (prefixWord ++ tailWord_1903002).sum := by decide
  have hdescent : baseEnd_1903002 < baseStart_1903002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903072 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1903072 : Nat := 118140960795 + 1903072 * 2 ^ 59
def prefixEnd_1903072 : Nat := 4983230072969 + 3 ^ 40 * 1903072 * 2
def baseEnd_1903072 : Nat := 977190656113283455747937

theorem tailTrace_1903072 : CollatzResearch.WordTrace tailWord_1903072 prefixEnd_1903072 977190656113283455747937 := by
  unfold tailWord_1903072
  simp only [CollatzResearch.WordTrace]
  refine ⟨34705369080751318833319735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46273825441001758444426313 34705369080751318833319735)
  ·
    refine ⟨52058053621126978249979603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34705369080751318833319735 52058053621126978249979603)
    ·
      refine ⟨78087080431690467374969405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52058053621126978249979603 78087080431690467374969405)
      ·
        refine ⟨29282655161883925265613527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78087080431690467374969405 29282655161883925265613527)
        ·
          refine ⟨43923982742825887898420291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29282655161883925265613527 43923982742825887898420291)
          ·
            refine ⟨65885974114238831847630437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43923982742825887898420291 65885974114238831847630437)
            ·
              refine ⟨12353620146419780971430707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65885974114238831847630437 12353620146419780971430707)
              ·
                refine ⟨18530430219629671457146061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12353620146419780971430707 18530430219629671457146061)
                ·
                  refine ⟨6948911332361126796429773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18530430219629671457146061 6948911332361126796429773)
                  ·
                    refine ⟨2605841749635422548661165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6948911332361126796429773 2605841749635422548661165)
                    ·
                      refine ⟨977190656113283455747937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605841749635422548661165 977190656113283455747937)
                      ·
                        rfl

theorem cell23_1903072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1903072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903072 prefixEnd_1903072 := by exact prefixLift 1903072
  have htrace : WordTrace (prefixWord ++ tailWord_1903072) baseStart_1903072 baseEnd_1903072 := by
    simpa [prefixWord, tailWord_1903072, baseEnd_1903072] using wordTrace_append hprefix tailTrace_1903072
  have hstable : (prefixWord ++ tailWord_1903072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903072).length < 2 ^ (prefixWord ++ tailWord_1903072).sum := by decide
  have hdescent : baseEnd_1903072 < baseStart_1903072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903089 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_1903089 : Nat := 118140960795 + 1903089 * 2 ^ 59
def prefixEnd_1903089 : Nat := 4983230072969 + 3 ^ 40 * 1903089 * 2
def baseEnd_1903089 : Nat := 977199385284409889235359

theorem tailTrace_1903089 : CollatzResearch.WordTrace tailWord_1903089 prefixEnd_1903089 977199385284409889235359 := by
  unfold tailWord_1903089
  simp only [CollatzResearch.WordTrace]
  refine ⟨69411358202441049570008321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46274238801627366380005547 69411358202441049570008321)
  ·
    refine ⟨52058518651830787177506241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69411358202441049570008321 52058518651830787177506241)
    ·
      refine ⟨39043888988873090383129681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52058518651830787177506241 39043888988873090383129681)
      ·
        refine ⟨29282916741654817787347261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39043888988873090383129681 29282916741654817787347261)
        ·
          refine ⟨10981093778120556670255223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29282916741654817787347261 10981093778120556670255223)
          ·
            refine ⟨16471640667180835005382835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981093778120556670255223 16471640667180835005382835)
            ·
              refine ⟨24707461000771252508074253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16471640667180835005382835 24707461000771252508074253)
              ·
                refine ⟨9265297875289219690527845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24707461000771252508074253 9265297875289219690527845)
                ·
                  refine ⟨1737243351616728691973971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9265297875289219690527845 1737243351616728691973971)
                  ·
                    refine ⟨2605865027425093037960957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737243351616728691973971 2605865027425093037960957)
                    ·
                      refine ⟨977199385284409889235359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605865027425093037960957 977199385284409889235359)
                      ·
                        rfl

theorem cell23_1903089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_1903089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903089 prefixEnd_1903089 := by exact prefixLift 1903089
  have htrace : WordTrace (prefixWord ++ tailWord_1903089) baseStart_1903089 baseEnd_1903089 := by
    simpa [prefixWord, tailWord_1903089, baseEnd_1903089] using wordTrace_append hprefix tailTrace_1903089
  have hstable : (prefixWord ++ tailWord_1903089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903089).length < 2 ^ (prefixWord ++ tailWord_1903089).sum := by decide
  have hdescent : baseEnd_1903089 < baseStart_1903089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903090 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1903090 : Nat := 118140960795 + 1903090 * 2 ^ 59
def prefixEnd_1903090 : Nat := 4983230072969 + 3 ^ 40 * 1903090 * 2
def baseEnd_1903090 : Nat := 977199898765064385322855

theorem tailTrace_1903090 : CollatzResearch.WordTrace tailWord_1903090 prefixEnd_1903090 977199898765064385322855 := by
  unfold tailWord_1903090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352848668859356685198681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46274263116958284493863149 17352848668859356685198681)
  ·
    refine ⟨13014636501644517513899011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17352848668859356685198681 13014636501644517513899011)
    ·
      refine ⟨19521954752466776270848517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13014636501644517513899011 19521954752466776270848517)
      ·
        refine ⟨3660366516087520550784097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19521954752466776270848517 3660366516087520550784097)
        ·
          refine ⟨2745274887065640413088073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3660366516087520550784097 2745274887065640413088073)
          ·
            refine ⟨2058956165299230309816055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745274887065640413088073 2058956165299230309816055)
            ·
              refine ⟨3088434247948845464724083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2058956165299230309816055 3088434247948845464724083)
              ·
                refine ⟨4632651371923268197086125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088434247948845464724083 4632651371923268197086125)
                ·
                  refine ⟨1737244264471225573907297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4632651371923268197086125 1737244264471225573907297)
                  ·
                    refine ⟨1302933198353419180430473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1737244264471225573907297 1302933198353419180430473)
                    ·
                      refine ⟨977199898765064385322855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302933198353419180430473 977199898765064385322855)
                      ·
                        rfl

theorem cell23_1903090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1903090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903090 prefixEnd_1903090 := by exact prefixLift 1903090
  have htrace : WordTrace (prefixWord ++ tailWord_1903090) baseStart_1903090 baseEnd_1903090 := by
    simpa [prefixWord, tailWord_1903090, baseEnd_1903090] using wordTrace_append hprefix tailTrace_1903090
  have hstable : (prefixWord ++ tailWord_1903090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903090).length < 2 ^ (prefixWord ++ tailWord_1903090).sum := by decide
  have hdescent : baseEnd_1903090 < baseStart_1903090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903095 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1903095 : Nat := 118140960795 + 1903095 * 2 ^ 59
def prefixEnd_1903095 : Nat := 4983230072969 + 3 ^ 40 * 1903095 * 2
def baseEnd_1903095 : Nat := 977202466168336865760331

theorem tailTrace_1903095 : CollatzResearch.WordTrace tailWord_1903095 prefixEnd_1903095 977202466168336865760331 := by
  unfold tailWord_1903095
  simp only [CollatzResearch.WordTrace]
  refine ⟨69411577040419312594726739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46274384693612875063151159 69411577040419312594726739)
  ·
    refine ⟨104117365560628968892090109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69411577040419312594726739 104117365560628968892090109)
    ·
      refine ⟨39044012085235863334533791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104117365560628968892090109 39044012085235863334533791)
      ·
        refine ⟨58566018127853795001800687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39044012085235863334533791 58566018127853795001800687)
        ·
          refine ⟨87849027191780692502701031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58566018127853795001800687 87849027191780692502701031)
          ·
            refine ⟨131773540787671038754051547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87849027191780692502701031 131773540787671038754051547)
            ·
              refine ⟨197660311181506558131077321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131773540787671038754051547 197660311181506558131077321)
              ·
                refine ⟨148245233386129918598307991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197660311181506558131077321 148245233386129918598307991)
                ·
                  refine ⟨222367850079194877897461987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148245233386129918598307991 222367850079194877897461987)
                  ·
                    refine ⟨333551775118792316846192981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 222367850079194877897461987 333551775118792316846192981)
                    ·
                      refine ⟨977202466168336865760331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 333551775118792316846192981 977202466168336865760331)
                      ·
                        rfl

theorem cell23_1903095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1903095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903095 prefixEnd_1903095 := by exact prefixLift 1903095
  have htrace : WordTrace (prefixWord ++ tailWord_1903095) baseStart_1903095 baseEnd_1903095 := by
    simpa [prefixWord, tailWord_1903095, baseEnd_1903095] using wordTrace_append hprefix tailTrace_1903095
  have hstable : (prefixWord ++ tailWord_1903095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903095).length < 2 ^ (prefixWord ++ tailWord_1903095).sum := by decide
  have hdescent : baseEnd_1903095 < baseStart_1903095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903110 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1903110 : Nat := 118140960795 + 1903110 * 2 ^ 59
def prefixEnd_1903110 : Nat := 4983230072969 + 3 ^ 40 * 1903110 * 2
def baseEnd_1903110 : Nat := 977210168378154307072763

theorem tailTrace_1903110 : CollatzResearch.WordTrace tailWord_1903110 prefixEnd_1903110 977210168378154307072763 := by
  unfold tailWord_1903110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169128879230155317391337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46274749423576646771015189 2169128879230155317391337)
  ·
    refine ⟨1626846659422616488043503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2169128879230155317391337 1626846659422616488043503)
    ·
      refine ⟨2440269989133924732065255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626846659422616488043503 2440269989133924732065255)
      ·
        refine ⟨3660404983700887098097883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440269989133924732065255 3660404983700887098097883)
        ·
          refine ⟨5490607475551330647146825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3660404983700887098097883 5490607475551330647146825)
          ·
            refine ⟨4117955606663497985360119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490607475551330647146825 4117955606663497985360119)
            ·
              refine ⟨6176933409995246978040179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117955606663497985360119 6176933409995246978040179)
              ·
                refine ⟨9265400114992870467060269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176933409995246978040179 9265400114992870467060269)
                ·
                  refine ⟨3474525043122326425147601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9265400114992870467060269 3474525043122326425147601)
                  ·
                    refine ⟨2605893782341744818860701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3474525043122326425147601 2605893782341744818860701)
                    ·
                      refine ⟨977210168378154307072763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605893782341744818860701 977210168378154307072763)
                      ·
                        rfl

theorem cell23_1903110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1903110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903110 prefixEnd_1903110 := by exact prefixLift 1903110
  have htrace : WordTrace (prefixWord ++ tailWord_1903110) baseStart_1903110 baseEnd_1903110 := by
    simpa [prefixWord, tailWord_1903110, baseEnd_1903110] using wordTrace_append hprefix tailTrace_1903110
  have hstable : (prefixWord ++ tailWord_1903110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903110).length < 2 ^ (prefixWord ++ tailWord_1903110).sum := by decide
  have hdescent : baseEnd_1903110 < baseStart_1903110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903116 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_1903116 : Nat := 118140960795 + 1903116 * 2 ^ 59
def prefixEnd_1903116 : Nat := 4983230072969 + 3 ^ 40 * 1903116 * 2
def baseEnd_1903116 : Nat := 977213249262081283597735

theorem tailTrace_1903116 : CollatzResearch.WordTrace tailWord_1903116 prefixEnd_1903116 977213249262081283597735 := by
  unfold tailWord_1903116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34706171486671616590620601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46274895315562155454160801 34706171486671616590620601)
  ·
    refine ⟨26029628615003712442965451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34706171486671616590620601 26029628615003712442965451)
    ·
      refine ⟨39044442922505568664448177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26029628615003712442965451 39044442922505568664448177)
      ·
        refine ⟨29283332191879176498336133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39044442922505568664448177 29283332191879176498336133)
        ·
          refine ⟨5490624785977345593438025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29283332191879176498336133 5490624785977345593438025)
          ·
            refine ⟨4117968589483009195078519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5490624785977345593438025 4117968589483009195078519)
            ·
              refine ⟨6176952884224513792617779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4117968589483009195078519 6176952884224513792617779)
              ·
                refine ⟨9265429326336770688926669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176952884224513792617779 9265429326336770688926669)
                ·
                  refine ⟨3474535997376289008347501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9265429326336770688926669 3474535997376289008347501)
                  ·
                    refine ⟨1302950999016108378130313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3474535997376289008347501 1302950999016108378130313)
                    ·
                      refine ⟨977213249262081283597735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302950999016108378130313 977213249262081283597735)
                      ·
                        rfl

theorem cell23_1903116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_1903116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903116 prefixEnd_1903116 := by exact prefixLift 1903116
  have htrace : WordTrace (prefixWord ++ tailWord_1903116) baseStart_1903116 baseEnd_1903116 := by
    simpa [prefixWord, tailWord_1903116, baseEnd_1903116] using wordTrace_append hprefix tailTrace_1903116
  have hstable : (prefixWord ++ tailWord_1903116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903116).length < 2 ^ (prefixWord ++ tailWord_1903116).sum := by decide
  have hdescent : baseEnd_1903116 < baseStart_1903116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903129 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 1, 4, 2]
def baseStart_1903129 : Nat := 118140960795 + 1903129 * 2 ^ 59
def prefixEnd_1903129 : Nat := 4983230072969 + 3 ^ 40 * 1903129 * 2
def baseEnd_1903129 : Nat := 977219924510589732735175

theorem tailTrace_1903129 : CollatzResearch.WordTrace tailWord_1903129 prefixEnd_1903129 977219924510589732735175 := by
  unfold tailWord_1903129
  simp only [CollatzResearch.WordTrace]
  refine ⟨69412817122296136401464441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46275211414864090934309627 69412817122296136401464441)
  ·
    refine ⟨52059612841722102301098331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69412817122296136401464441 52059612841722102301098331)
    ·
      refine ⟨78089419262583153451647497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52059612841722102301098331 78089419262583153451647497)
      ·
        refine ⟨58567064446937365088735623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78089419262583153451647497 58567064446937365088735623)
        ·
          refine ⟨87850596670406047633103435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58567064446937365088735623 87850596670406047633103435)
          ·
            refine ⟨131775895005609071449655153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87850596670406047633103435 131775895005609071449655153)
            ·
              refine ⟨98831921254206803587241365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131775895005609071449655153 98831921254206803587241365)
              ·
                refine ⟨4632746308790943918151939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98831921254206803587241365 4632746308790943918151939)
                ·
                  refine ⟨6949119463186415877227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4632746308790943918151939 6949119463186415877227909)
                  ·
                    refine ⟨1302959899347452976980233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6949119463186415877227909 1302959899347452976980233)
                    ·
                      refine ⟨977219924510589732735175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1302959899347452976980233 977219924510589732735175)
                      ·
                        rfl

theorem cell23_1903129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_1903129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903129 prefixEnd_1903129 := by exact prefixLift 1903129
  have htrace : WordTrace (prefixWord ++ tailWord_1903129) baseStart_1903129 baseEnd_1903129 := by
    simpa [prefixWord, tailWord_1903129, baseEnd_1903129] using wordTrace_append hprefix tailTrace_1903129
  have hstable : (prefixWord ++ tailWord_1903129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903129).length < 2 ^ (prefixWord ++ tailWord_1903129).sum := by decide
  have hdescent : baseEnd_1903129 < baseStart_1903129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903140 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1903140 : Nat := 118140960795 + 1903140 * 2 ^ 59
def prefixEnd_1903140 : Nat := 4983230072969 + 3 ^ 40 * 1903140 * 2
def baseEnd_1903140 : Nat := 977225572797789189697625

theorem tailTrace_1903140 : CollatzResearch.WordTrace tailWord_1903140 prefixEnd_1903140 977225572797789189697625 := by
  unfold tailWord_1903140
  simp only [CollatzResearch.WordTrace]
  refine ⟨34706609162628142640057437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46275478883504190186743249 34706609162628142640057437)
  ·
    refine ⟨13014978435985553490021539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34706609162628142640057437 13014978435985553490021539)
    ·
      refine ⟨19522467653978330235032309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13014978435985553490021539 19522467653978330235032309)
      ·
        refine ⟨1830231342560468459534279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19522467653978330235032309 1830231342560468459534279)
        ·
          refine ⟨2745347013840702689301419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830231342560468459534279 2745347013840702689301419)
          ·
            refine ⟨4118020520761054033952129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745347013840702689301419 4118020520761054033952129)
            ·
              refine ⟨3088515390570790525464097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4118020520761054033952129 3088515390570790525464097)
              ·
                refine ⟨2316386542928092894098073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088515390570790525464097 2316386542928092894098073)
                ·
                  refine ⟨1737289907196069670573555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316386542928092894098073 1737289907196069670573555)
                  ·
                    refine ⟨2605934860794104505860333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737289907196069670573555 2605934860794104505860333)
                    ·
                      refine ⟨977225572797789189697625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2605934860794104505860333 977225572797789189697625)
                      ·
                        rfl

theorem cell23_1903140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1903140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903140 prefixEnd_1903140 := by exact prefixLift 1903140
  have htrace : WordTrace (prefixWord ++ tailWord_1903140) baseStart_1903140 baseEnd_1903140 := by
    simpa [prefixWord, tailWord_1903140, baseEnd_1903140] using wordTrace_append hprefix tailTrace_1903140
  have hstable : (prefixWord ++ tailWord_1903140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903140).length < 2 ^ (prefixWord ++ tailWord_1903140).sum := by decide
  have hdescent : baseEnd_1903140 < baseStart_1903140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903169 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 7]
def baseStart_1903169 : Nat := 118140960795 + 1903169 * 2 ^ 59
def prefixEnd_1903169 : Nat := 4983230072969 + 3 ^ 40 * 1903169 * 2
def baseEnd_1903169 : Nat := 108582273748529952914999

theorem tailTrace_1903169 : CollatzResearch.WordTrace tailWord_1903169 prefixEnd_1903169 108582273748529952914999 := by
  unfold tailWord_1903169
  simp only [CollatzResearch.WordTrace]
  refine ⟨69414276042151223232920561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46276184028100815488613707 69414276042151223232920561)
  ·
    refine ⟨52060707031613417424690421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69414276042151223232920561 52060707031613417424690421)
    ·
      refine ⟨4880691284213757883564727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52060707031613417424690421 4880691284213757883564727)
      ·
        refine ⟨7321036926320636825347091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880691284213757883564727 7321036926320636825347091)
        ·
          refine ⟨10981555389480955238020637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321036926320636825347091 10981555389480955238020637)
          ·
            refine ⟨4118083271055358214257739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10981555389480955238020637 4118083271055358214257739)
            ·
              refine ⟨6177124906583037321386609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118083271055358214257739 6177124906583037321386609)
              ·
                refine ⟨4632843679937277991039957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177124906583037321386609 4632843679937277991039957)
                ·
                  refine ⟨108582273748529952914999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4632843679937277991039957 108582273748529952914999)
                  ·
                    rfl

theorem cell23_1903169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_1903169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903169 prefixEnd_1903169 := by exact prefixLift 1903169
  have htrace : WordTrace (prefixWord ++ tailWord_1903169) baseStart_1903169 baseEnd_1903169 := by
    simpa [prefixWord, tailWord_1903169, baseEnd_1903169] using wordTrace_append hprefix tailTrace_1903169
  have hstable : (prefixWord ++ tailWord_1903169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903169).length < 2 ^ (prefixWord ++ tailWord_1903169).sum := by decide
  have hdescent : baseEnd_1903169 < baseStart_1903169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903186 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1903186 : Nat := 118140960795 + 1903186 * 2 ^ 59
def prefixEnd_1903186 : Nat := 4983230072969 + 3 ^ 40 * 1903186 * 2
def baseEnd_1903186 : Nat := 108583243656432889969157

theorem tailTrace_1903186 : CollatzResearch.WordTrace tailWord_1903186 prefixEnd_1903186 108583243656432889969157 := by
  unfold tailWord_1903186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17353724020772408784072353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46276597388726423424192941 17353724020772408784072353)
  ·
    refine ⟨13015293015579306588054265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17353724020772408784072353 13015293015579306588054265)
    ·
      refine ⟨9761469761684479941040699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13015293015579306588054265 9761469761684479941040699)
      ·
        refine ⟨14642204642526719911561049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9761469761684479941040699 14642204642526719911561049)
        ·
          refine ⟨10981653481895039933670787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14642204642526719911561049 10981653481895039933670787)
          ·
            refine ⟨16472480222842559900506181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10981653481895039933670787 16472480222842559900506181)
            ·
              refine ⟨3088590041782979981344909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16472480222842559900506181 3088590041782979981344909)
              ·
                refine ⟨1158221265668617493004341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3088590041782979981344909 1158221265668617493004341)
                ·
                  refine ⟨108583243656432889969157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158221265668617493004341 108583243656432889969157)
                  ·
                    rfl

theorem cell23_1903186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1903186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903186 prefixEnd_1903186 := by exact prefixLift 1903186
  have htrace : WordTrace (prefixWord ++ tailWord_1903186) baseStart_1903186 baseEnd_1903186 := by
    simpa [prefixWord, tailWord_1903186, baseEnd_1903186] using wordTrace_append hprefix tailTrace_1903186
  have hstable : (prefixWord ++ tailWord_1903186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903186).length < 2 ^ (prefixWord ++ tailWord_1903186).sum := by decide
  have hdescent : baseEnd_1903186 < baseStart_1903186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903192 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1903192 : Nat := 118140960795 + 1903192 * 2 ^ 59
def prefixEnd_1903192 : Nat := 4983230072969 + 3 ^ 40 * 1903192 * 2
def baseEnd_1903192 : Nat := 977252273791822986247385

theorem tailTrace_1903192 : CollatzResearch.WordTrace tailWord_1903192 prefixEnd_1903192 977252273791822986247385 := by
  unfold tailWord_1903192
  simp only [CollatzResearch.WordTrace]
  refine ⟨34707557460533949080503915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46276743280711932107338553 34707557460533949080503915)
  ·
    refine ⟨52061336190800923620755873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34707557460533949080503915 52061336190800923620755873)
    ·
      refine ⟨39046002143100692715566905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52061336190800923620755873 39046002143100692715566905)
      ·
        refine ⟨29284501607325519536675179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39046002143100692715566905 29284501607325519536675179)
        ·
          refine ⟨43926752410988279305012769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29284501607325519536675179 43926752410988279305012769)
          ·
            refine ⟨32945064308241209478759577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43926752410988279305012769 32945064308241209478759577)
            ·
              refine ⟨24708798231180907109069683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32945064308241209478759577 24708798231180907109069683)
              ·
                refine ⟨37063197346771360663604525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24708798231180907109069683 37063197346771360663604525)
                ·
                  refine ⟨13898699005039260248851697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37063197346771360663604525 13898699005039260248851697)
                  ·
                    refine ⟨10424024253779445186638773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13898699005039260248851697 10424024253779445186638773)
                    ·
                      refine ⟨977252273791822986247385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10424024253779445186638773 977252273791822986247385)
                      ·
                        rfl

theorem cell23_1903192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1903192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903192 prefixEnd_1903192 := by exact prefixLift 1903192
  have htrace : WordTrace (prefixWord ++ tailWord_1903192) baseStart_1903192 baseEnd_1903192 := by
    simpa [prefixWord, tailWord_1903192, baseEnd_1903192] using wordTrace_append hprefix tailTrace_1903192
  have hstable : (prefixWord ++ tailWord_1903192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903192).length < 2 ^ (prefixWord ++ tailWord_1903192).sum := by decide
  have hdescent : baseEnd_1903192 < baseStart_1903192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903219 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 6, 2]
def baseStart_1903219 : Nat := 118140960795 + 1903219 * 2 ^ 59
def prefixEnd_1903219 : Nat := 4983230072969 + 3 ^ 40 * 1903219 * 2
def baseEnd_1903219 : Nat := 977266137769494380609761

theorem tailTrace_1903219 : CollatzResearch.WordTrace tailWord_1903219 prefixEnd_1903219 977266137769494380609761 := by
  unfold tailWord_1903219
  simp only [CollatzResearch.WordTrace]
  refine ⟨69416099691970081772240711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46277399794646721181493807 69416099691970081772240711)
  ·
    refine ⟨104124149537955122658361067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69416099691970081772240711 104124149537955122658361067)
    ·
      refine ⟨156186224306932683987541601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104124149537955122658361067 156186224306932683987541601)
      ·
        refine ⟨117139668230199512990656201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156186224306932683987541601 117139668230199512990656201)
        ·
          refine ⟨87854751172649634742992151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117139668230199512990656201 87854751172649634742992151)
          ·
            refine ⟨131782126758974452114488227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87854751172649634742992151 131782126758974452114488227)
            ·
              refine ⟨197673190138461678171732341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131782126758974452114488227 197673190138461678171732341)
              ·
                refine ⟨18531861575480782328599907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197673190138461678171732341 18531861575480782328599907)
                ·
                  refine ⟨27797792363221173492899861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18531861575480782328599907 27797792363221173492899861)
                  ·
                    refine ⟨1303021517025992507479681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27797792363221173492899861 1303021517025992507479681)
                    ·
                      refine ⟨977266137769494380609761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303021517025992507479681 977266137769494380609761)
                      ·
                        rfl

theorem cell23_1903219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6, 2].length) (baseStart_1903219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903219 prefixEnd_1903219 := by exact prefixLift 1903219
  have htrace : WordTrace (prefixWord ++ tailWord_1903219) baseStart_1903219 baseEnd_1903219 := by
    simpa [prefixWord, tailWord_1903219, baseEnd_1903219] using wordTrace_append hprefix tailTrace_1903219
  have hstable : (prefixWord ++ tailWord_1903219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903219).length < 2 ^ (prefixWord ++ tailWord_1903219).sum := by decide
  have hdescent : baseEnd_1903219 < baseStart_1903219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903239 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1903239 : Nat := 118140960795 + 1903239 * 2 ^ 59
def prefixEnd_1903239 : Nat := 4983230072969 + 3 ^ 40 * 1903239 * 2
def baseEnd_1903239 : Nat := 977276407382584302359669

theorem tailTrace_1903239 : CollatzResearch.WordTrace tailWord_1903239 prefixEnd_1903239 977276407382584302359669 := by
  unfold tailWord_1903239
  simp only [CollatzResearch.WordTrace]
  refine ⟨69416829151897625187968771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46277886101265083458645847 69416829151897625187968771)
  ·
    refine ⟨104125243727846437781953157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69416829151897625187968771 104125243727846437781953157)
    ·
      refine ⟨19523483198971207084116217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104125243727846437781953157 19523483198971207084116217)
      ·
        refine ⟨14642612399228405313087163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19523483198971207084116217 14642612399228405313087163)
        ·
          refine ⟨21963918598842607969630745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14642612399228405313087163 21963918598842607969630745)
          ·
            refine ⟨16472938949131955977223059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21963918598842607969630745 16472938949131955977223059)
            ·
              refine ⟨24709408423697933965834589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472938949131955977223059 24709408423697933965834589)
              ·
                refine ⟨9266028158886725237187971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24709408423697933965834589 9266028158886725237187971)
                ·
                  refine ⟨13899042238330087855781957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9266028158886725237187971 13899042238330087855781957)
                  ·
                    refine ⟨2606070419686891472959117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13899042238330087855781957 2606070419686891472959117)
                    ·
                      refine ⟨977276407382584302359669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606070419686891472959117 977276407382584302359669)
                      ·
                        rfl

theorem cell23_1903239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1903239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903239 prefixEnd_1903239 := by exact prefixLift 1903239
  have htrace : WordTrace (prefixWord ++ tailWord_1903239) baseStart_1903239 baseEnd_1903239 := by
    simpa [prefixWord, tailWord_1903239, baseEnd_1903239] using wordTrace_append hprefix tailTrace_1903239
  have hstable : (prefixWord ++ tailWord_1903239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903239).length < 2 ^ (prefixWord ++ tailWord_1903239).sum := by decide
  have hdescent : baseEnd_1903239 < baseStart_1903239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903256 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1903256 : Nat := 118140960795 + 1903256 * 2 ^ 59
def prefixEnd_1903256 : Nat := 4983230072969 + 3 ^ 40 * 1903256 * 2
def baseEnd_1903256 : Nat := 977285136553710735847091

theorem tailTrace_1903256 : CollatzResearch.WordTrace tailWord_1903256 prefixEnd_1903256 977285136553710735847091 := by
  unfold tailWord_1903256
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708724596418018545668811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46278299461890691394225081 34708724596418018545668811)
  ·
    refine ⟨52063086894627027818503217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34708724596418018545668811 52063086894627027818503217)
    ·
      refine ⟨39047315170970270863877413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52063086894627027818503217 39047315170970270863877413)
      ·
        refine ⟨7321371594556925786977015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39047315170970270863877413 7321371594556925786977015)
        ·
          refine ⟨10982057391835388680465523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321371594556925786977015 10982057391835388680465523)
          ·
            refine ⟨16473086087753083020698285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10982057391835388680465523 16473086087753083020698285)
            ·
              refine ⟨6177407282907406132761857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16473086087753083020698285 6177407282907406132761857)
              ·
                refine ⟨4633055462180554599571393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177407282907406132761857 4633055462180554599571393)
                ·
                  refine ⟨3474791596635415949678545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4633055462180554599571393 3474791596635415949678545)
                  ·
                    refine ⟨2606093697476561962258909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3474791596635415949678545 2606093697476561962258909)
                    ·
                      refine ⟨977285136553710735847091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606093697476561962258909 977285136553710735847091)
                      ·
                        rfl

theorem cell23_1903256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1903256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903256 prefixEnd_1903256 := by exact prefixLift 1903256
  have htrace : WordTrace (prefixWord ++ tailWord_1903256) baseStart_1903256 baseEnd_1903256 := by
    simpa [prefixWord, tailWord_1903256, baseEnd_1903256] using wordTrace_append hprefix tailTrace_1903256
  have hstable : (prefixWord ++ tailWord_1903256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903256).length < 2 ^ (prefixWord ++ tailWord_1903256).sum := by decide
  have hdescent : baseEnd_1903256 < baseStart_1903256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903314 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1903314 : Nat := 118140960795 + 1903314 * 2 ^ 59
def prefixEnd_1903314 : Nat := 4983230072969 + 3 ^ 40 * 1903314 * 2
def baseEnd_1903314 : Nat := 325771639477223836307275

theorem tailTrace_1903314 : CollatzResearch.WordTrace tailWord_1903314 prefixEnd_1903314 325771639477223836307275 := by
  unfold tailWord_1903314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17354891156656478249237249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46279709751083941997965997 17354891156656478249237249)
  ·
    refine ⟨13016168367492358686927937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17354891156656478249237249 13016168367492358686927937)
    ·
      refine ⟨9762126275619269015195953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13016168367492358686927937 9762126275619269015195953)
      ·
        refine ⟨7321594706714451761396965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9762126275619269015195953 7321594706714451761396965)
        ·
          refine ⟨1372799007508959705261931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7321594706714451761396965 1372799007508959705261931)
          ·
            refine ⟨2059198511263439557892897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372799007508959705261931 2059198511263439557892897)
            ·
              refine ⟨1544398883447579668419673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059198511263439557892897 1544398883447579668419673)
              ·
                refine ⟨1158299162585684751314755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544398883447579668419673 1158299162585684751314755)
                ·
                  refine ⟨1737448743878527126972133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158299162585684751314755 1737448743878527126972133)
                  ·
                    refine ⟨325771639477223836307275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1737448743878527126972133 325771639477223836307275)
                    ·
                      rfl

theorem cell23_1903314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1903314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903314 prefixEnd_1903314 := by exact prefixLift 1903314
  have htrace : WordTrace (prefixWord ++ tailWord_1903314) baseStart_1903314 baseEnd_1903314 := by
    simpa [prefixWord, tailWord_1903314, baseEnd_1903314] using wordTrace_append hprefix tailTrace_1903314
  have hstable : (prefixWord ++ tailWord_1903314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903314).length < 2 ^ (prefixWord ++ tailWord_1903314).sum := by decide
  have hdescent : baseEnd_1903314 < baseStart_1903314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903320 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 1, 1, 3]
def baseStart_1903320 : Nat := 118140960795 + 1903320 * 2 ^ 59
def prefixEnd_1903320 : Nat := 4983230072969 + 3 ^ 40 * 1903320 * 2
def baseEnd_1903320 : Nat := 977317999315598485446797

theorem tailTrace_1903320 : CollatzResearch.WordTrace tailWord_1903320 prefixEnd_1903320 977317999315598485446797 := by
  unfold tailWord_1903320
  simp only [CollatzResearch.WordTrace]
  refine ⟨34709891732302088010833707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46279855643069450681111609 34709891732302088010833707)
  ·
    refine ⟨52064837598453132016250561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34709891732302088010833707 52064837598453132016250561)
    ·
      refine ⟨39048628198839849012187921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52064837598453132016250561 39048628198839849012187921)
      ·
        refine ⟨29286471149129886759140941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39048628198839849012187921 29286471149129886759140941)
        ·
          refine ⟨10982426680923707534677853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29286471149129886759140941 10982426680923707534677853)
          ·
            refine ⟨4118410005346390325504195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10982426680923707534677853 4118410005346390325504195)
            ·
              refine ⟨6177615008019585488256293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4118410005346390325504195 6177615008019585488256293)
              ·
                refine ⟨1158302814003672279048055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6177615008019585488256293 1158302814003672279048055)
                ·
                  refine ⟨1737454221005508418572083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158302814003672279048055 1737454221005508418572083)
                  ·
                    refine ⟨2606181331508262627858125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737454221005508418572083 2606181331508262627858125)
                    ·
                      refine ⟨977317999315598485446797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606181331508262627858125 977317999315598485446797)
                      ·
                        rfl

theorem cell23_1903320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_1903320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903320 prefixEnd_1903320 := by exact prefixLift 1903320
  have htrace : WordTrace (prefixWord ++ tailWord_1903320) baseStart_1903320 baseEnd_1903320 := by
    simpa [prefixWord, tailWord_1903320, baseEnd_1903320] using wordTrace_append hprefix tailTrace_1903320
  have hstable : (prefixWord ++ tailWord_1903320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903320).length < 2 ^ (prefixWord ++ tailWord_1903320).sum := by decide
  have hdescent : baseEnd_1903320 < baseStart_1903320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903343 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 5, 2, 2]
def baseStart_1903343 : Nat := 118140960795 + 1903343 * 2 ^ 59
def prefixEnd_1903343 : Nat := 4983230072969 + 3 ^ 40 * 1903343 * 2
def baseEnd_1903343 : Nat := 977329809370651895459191

theorem tailTrace_1903343 : CollatzResearch.WordTrace tailWord_1903343 prefixEnd_1903343 977329809370651895459191 := by
  unfold tailWord_1903343
  simp only [CollatzResearch.WordTrace]
  refine ⟨69420622343520850949754683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46280414895680567299836455 69420622343520850949754683)
  ·
    refine ⟨104130933515281276424632025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69420622343520850949754683 104130933515281276424632025)
    ·
      refine ⟨78098200136460957318474019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104130933515281276424632025 78098200136460957318474019)
      ·
        refine ⟨117147300204691435977711029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78098200136460957318474019 117147300204691435977711029)
        ·
          refine ⟨10982559394189822122910409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117147300204691435977711029 10982559394189822122910409)
          ·
            refine ⟨8236919545642366592182807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10982559394189822122910409 8236919545642366592182807)
            ·
              refine ⟨12355379318463549888274211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8236919545642366592182807 12355379318463549888274211)
              ·
                refine ⟨18533068977695324832411317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12355379318463549888274211 18533068977695324832411317)
                ·
                  refine ⟨1737475216658936703038561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18533068977695324832411317 1737475216658936703038561)
                  ·
                    refine ⟨1303106412494202527278921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1737475216658936703038561 1303106412494202527278921)
                    ·
                      refine ⟨977329809370651895459191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303106412494202527278921 977329809370651895459191)
                      ·
                        rfl

theorem cell23_1903343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2, 2].length) (baseStart_1903343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903343 prefixEnd_1903343 := by exact prefixLift 1903343
  have htrace : WordTrace (prefixWord ++ tailWord_1903343) baseStart_1903343 baseEnd_1903343 := by
    simpa [prefixWord, tailWord_1903343, baseEnd_1903343] using wordTrace_append hprefix tailTrace_1903343
  have hstable : (prefixWord ++ tailWord_1903343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903343).length < 2 ^ (prefixWord ++ tailWord_1903343).sum := by decide
  have hdescent : baseEnd_1903343 < baseStart_1903343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903356 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1903356 : Nat := 118140960795 + 1903356 * 2 ^ 59
def prefixEnd_1903356 : Nat := 4983230072969 + 3 ^ 40 * 1903356 * 2
def baseEnd_1903356 : Nat := 977336484619160344596631

theorem tailTrace_1903356 : CollatzResearch.WordTrace tailWord_1903356 prefixEnd_1903356 977336484619160344596631 := by
  unfold tailWord_1903356
  simp only [CollatzResearch.WordTrace]
  refine ⟨34710548246236877084988961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46280730994982502779985281 34710548246236877084988961)
  ·
    refine ⟨26032911184677657813741721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34710548246236877084988961 26032911184677657813741721)
    ·
      refine ⟨19524683388508243360306291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26032911184677657813741721 19524683388508243360306291)
      ·
        refine ⟨29287025082762365040459437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19524683388508243360306291 29287025082762365040459437)
        ·
          refine ⟨10982634406035886890172289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29287025082762365040459437 10982634406035886890172289)
          ·
            refine ⟨8236975804526915167629217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10982634406035886890172289 8236975804526915167629217)
            ·
              refine ⟨6177731853395186375721913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8236975804526915167629217 6177731853395186375721913)
              ·
                refine ⟨4633298890046389781791435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6177731853395186375721913 4633298890046389781791435)
                ·
                  refine ⟨6949948335069584672687153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633298890046389781791435 6949948335069584672687153)
                  ·
                    refine ⟨5212461251302188504515365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6949948335069584672687153 5212461251302188504515365)
                    ·
                      refine ⟨977336484619160344596631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5212461251302188504515365 977336484619160344596631)
                      ·
                        rfl

theorem cell23_1903356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1903356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903356 prefixEnd_1903356 := by exact prefixLift 1903356
  have htrace : WordTrace (prefixWord ++ tailWord_1903356) baseStart_1903356 baseEnd_1903356 := by
    simpa [prefixWord, tailWord_1903356, baseEnd_1903356] using wordTrace_append hprefix tailTrace_1903356
  have hstable : (prefixWord ++ tailWord_1903356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903356).length < 2 ^ (prefixWord ++ tailWord_1903356).sum := by decide
  have hdescent : baseEnd_1903356 < baseStart_1903356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903403 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 1, 3, 2]
def baseStart_1903403 : Nat := 118140960795 + 1903403 * 2 ^ 59
def prefixEnd_1903403 : Nat := 4983230072969 + 3 ^ 40 * 1903403 * 2
def baseEnd_1903403 : Nat := 977360618209921660708915

theorem tailTrace_1903403 : CollatzResearch.WordTrace tailWord_1903403 prefixEnd_1903403 977360618209921660708915 := by
  unfold tailWord_1903403
  simp only [CollatzResearch.WordTrace]
  refine ⟨69422810723303481196938863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46281873815535654131292575 69422810723303481196938863)
  ·
    refine ⟨104134216084955221795408295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69422810723303481196938863 104134216084955221795408295)
    ·
      refine ⟨156201324127432832693112443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104134216084955221795408295 156201324127432832693112443)
      ·
        refine ⟨234301986191149249039668665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156201324127432832693112443 234301986191149249039668665)
        ·
          refine ⟨175726489643361936779751499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234301986191149249039668665 175726489643361936779751499)
          ·
            refine ⟨263589734465042905169627249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175726489643361936779751499 263589734465042905169627249)
            ·
              refine ⟨197692300848782178877220437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263589734465042905169627249 197692300848782178877220437)
              ·
                refine ⟨2316706650571666158717427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 197692300848782178877220437 2316706650571666158717427)
                ·
                  refine ⟨3475059975857499238076141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2316706650571666158717427 3475059975857499238076141)
                  ·
                    refine ⟨1303147490946562214278553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3475059975857499238076141 1303147490946562214278553)
                    ·
                      refine ⟨977360618209921660708915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303147490946562214278553 977360618209921660708915)
                      ·
                        rfl

theorem cell23_1903403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3, 2].length) (baseStart_1903403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903403 prefixEnd_1903403 := by exact prefixLift 1903403
  have htrace : WordTrace (prefixWord ++ tailWord_1903403) baseStart_1903403 baseEnd_1903403 := by
    simpa [prefixWord, tailWord_1903403, baseEnd_1903403] using wordTrace_append hprefix tailTrace_1903403
  have hstable : (prefixWord ++ tailWord_1903403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903403).length < 2 ^ (prefixWord ++ tailWord_1903403).sum := by decide
  have hdescent : baseEnd_1903403 < baseStart_1903403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903428 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1903428 : Nat := 118140960795 + 1903428 * 2 ^ 59
def prefixEnd_1903428 : Nat := 4983230072969 + 3 ^ 40 * 1903428 * 2
def baseEnd_1903428 : Nat := 977373455226284062896301

theorem tailTrace_1903428 : CollatzResearch.WordTrace tailWord_1903428 prefixEnd_1903428 977373455226284062896301 := by
  unfold tailWord_1903428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34711861274106455233299469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46282481698808606977732625 34711861274106455233299469)
  ·
    refine ⟨13016947977789920712487301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34711861274106455233299469 13016947977789920712487301)
    ·
      refine ⟨2440677745835610133591369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13016947977789920712487301 2440677745835610133591369)
      ·
        refine ⟨1830508309376707600193527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2440677745835610133591369 1830508309376707600193527)
        ·
          refine ⟨2745762464065061400290291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830508309376707600193527 2745762464065061400290291)
          ·
            refine ⟨4118643696097592100435437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745762464065061400290291 4118643696097592100435437)
            ·
              refine ⟨1544491386036597037663289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4118643696097592100435437 1544491386036597037663289)
              ·
                refine ⟨1158368539527447778247467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544491386036597037663289 1158368539527447778247467)
                ·
                  refine ⟨1737552809291171667371201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158368539527447778247467 1737552809291171667371201)
                  ·
                    refine ⟨1303164606968378750528401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1737552809291171667371201 1303164606968378750528401)
                    ·
                      refine ⟨977373455226284062896301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303164606968378750528401 977373455226284062896301)
                      ·
                        rfl

theorem cell23_1903428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1903428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903428 prefixEnd_1903428 := by exact prefixLift 1903428
  have htrace : WordTrace (prefixWord ++ tailWord_1903428) baseStart_1903428 baseEnd_1903428 := by
    simpa [prefixWord, tailWord_1903428, baseEnd_1903428] using wordTrace_append hprefix tailTrace_1903428
  have hstable : (prefixWord ++ tailWord_1903428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903428).length < 2 ^ (prefixWord ++ tailWord_1903428).sum := by decide
  have hdescent : baseEnd_1903428 < baseStart_1903428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903429 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1903429 : Nat := 118140960795 + 1903429 * 2 ^ 59
def prefixEnd_1903429 : Nat := 4983230072969 + 3 ^ 40 * 1903429 * 2
def baseEnd_1903429 : Nat := 977373968706938558983795

theorem tailTrace_1903429 : CollatzResearch.WordTrace tailWord_1903429 prefixEnd_1903429 977373968706938558983795 := by
  unfold tailWord_1903429
  simp only [CollatzResearch.WordTrace]
  refine ⟨69423759021209287637385341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46282506014139525091590227 69423759021209287637385341)
  ·
    refine ⟨26033909632953482864019503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69423759021209287637385341 26033909632953482864019503)
    ·
      refine ⟨39050864449430224296029255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26033909632953482864019503 39050864449430224296029255)
      ·
        refine ⟨58576296674145336444043883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39050864449430224296029255 58576296674145336444043883)
        ·
          refine ⟨87864445011218004666065825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58576296674145336444043883 87864445011218004666065825)
          ·
            refine ⟨65898333758413503499549369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87864445011218004666065825 65898333758413503499549369)
            ·
              refine ⟨49423750318810127624662027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65898333758413503499549369 49423750318810127624662027)
              ·
                refine ⟨74135625478215191436993041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49423750318810127624662027 74135625478215191436993041)
                ·
                  refine ⟨55601719108661393577744781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74135625478215191436993041 55601719108661393577744781)
                  ·
                    refine ⟨20850644665748022591654293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55601719108661393577744781 20850644665748022591654293)
                    ·
                      refine ⟨977373968706938558983795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20850644665748022591654293 977373968706938558983795)
                      ·
                        rfl

theorem cell23_1903429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1903429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903429 prefixEnd_1903429 := by exact prefixLift 1903429
  have htrace : WordTrace (prefixWord ++ tailWord_1903429) baseStart_1903429 baseEnd_1903429 := by
    simpa [prefixWord, tailWord_1903429, baseEnd_1903429] using wordTrace_append hprefix tailTrace_1903429
  have hstable : (prefixWord ++ tailWord_1903429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903429).length < 2 ^ (prefixWord ++ tailWord_1903429).sum := by decide
  have hdescent : baseEnd_1903429 < baseStart_1903429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903444 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_1903444 : Nat := 118140960795 + 1903444 * 2 ^ 59
def prefixEnd_1903444 : Nat := 4983230072969 + 3 ^ 40 * 1903444 * 2
def baseEnd_1903444 : Nat := 977381670916756000296227

theorem tailTrace_1903444 : CollatzResearch.WordTrace tailWord_1903444 prefixEnd_1903444 977381670916756000296227 := by
  unfold tailWord_1903444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34712153058077472599590693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46282870744103296799454257 34712153058077472599590693)
  ·
    refine ⟨6508528698389526112423255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34712153058077472599590693 6508528698389526112423255)
    ·
      refine ⟨9762793047584289168634883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508528698389526112423255 9762793047584289168634883)
      ·
        refine ⟨14644189571376433752952325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9762793047584289168634883 14644189571376433752952325)
        ·
          refine ⟨2745785544633081328678561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14644189571376433752952325 2745785544633081328678561)
          ·
            refine ⟨2059339158474810996508921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745785544633081328678561 2059339158474810996508921)
            ·
              refine ⟨1544504368856108247381691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059339158474810996508921 1544504368856108247381691)
              ·
                refine ⟨2316756553284162371072537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544504368856108247381691 2316756553284162371072537)
                ·
                  refine ⟨1737567414963121778304403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316756553284162371072537 1737567414963121778304403)
                  ·
                    refine ⟨2606351122444682667456605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737567414963121778304403 2606351122444682667456605)
                    ·
                      refine ⟨977381670916756000296227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606351122444682667456605 977381670916756000296227)
                      ·
                        rfl

theorem cell23_1903444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_1903444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903444 prefixEnd_1903444 := by exact prefixLift 1903444
  have htrace : WordTrace (prefixWord ++ tailWord_1903444) baseStart_1903444 baseEnd_1903444 := by
    simpa [prefixWord, tailWord_1903444, baseEnd_1903444] using wordTrace_append hprefix tailTrace_1903444
  have hstable : (prefixWord ++ tailWord_1903444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903444).length < 2 ^ (prefixWord ++ tailWord_1903444).sum := by decide
  have hdescent : baseEnd_1903444 < baseStart_1903444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903493 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_1903493 : Nat := 118140960795 + 1903493 * 2 ^ 59
def prefixEnd_1903493 : Nat := 4983230072969 + 3 ^ 40 * 1903493 * 2
def baseEnd_1903493 : Nat := 977406831468826308583501

theorem tailTrace_1903493 : CollatzResearch.WordTrace tailWord_1903493 prefixEnd_1903493 977406831468826308583501 := by
  unfold tailWord_1903493
  simp only [CollatzResearch.WordTrace]
  refine ⟨69426093292977426567715133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46284062195318284378476755 69426093292977426567715133)
  ·
    refine ⟨26034784984866534962893175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69426093292977426567715133 26034784984866534962893175)
    ·
      refine ⟨39052177477299802444339763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26034784984866534962893175 39052177477299802444339763)
      ·
        refine ⟨58578266215949703666509645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39052177477299802444339763 58578266215949703666509645)
        ·
          refine ⟨21966849830981138874941117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58578266215949703666509645 21966849830981138874941117)
          ·
            refine ⟨8237568686617927078102919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21966849830981138874941117 8237568686617927078102919)
            ·
              refine ⟨12356353029926890617154379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8237568686617927078102919 12356353029926890617154379)
              ·
                refine ⟨18534529544890335925731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12356353029926890617154379 18534529544890335925731569)
                ·
                  refine ⟨13900897158667751944298677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18534529544890335925731569 13900897158667751944298677)
                  ·
                    refine ⟨1303209108625101744778001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13900897158667751944298677 1303209108625101744778001)
                    ·
                      refine ⟨977406831468826308583501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303209108625101744778001 977406831468826308583501)
                      ·
                        rfl

theorem cell23_1903493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_1903493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903493 prefixEnd_1903493 := by exact prefixLift 1903493
  have htrace : WordTrace (prefixWord ++ tailWord_1903493) baseStart_1903493 baseEnd_1903493 := by
    simpa [prefixWord, tailWord_1903493, baseEnd_1903493] using wordTrace_append hprefix tailTrace_1903493
  have hstable : (prefixWord ++ tailWord_1903493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903493).length < 2 ^ (prefixWord ++ tailWord_1903493).sum := by decide
  have hdescent : baseEnd_1903493 < baseStart_1903493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903523 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1903523 : Nat := 118140960795 + 1903523 * 2 ^ 59
def prefixEnd_1903523 : Nat := 4983230072969 + 3 ^ 40 * 1903523 * 2
def baseEnd_1903523 : Nat := 977422235888461191208363

theorem tailTrace_1903523 : CollatzResearch.WordTrace tailWord_1903523 prefixEnd_1903523 977422235888461191208363 := by
  unfold tailWord_1903523
  simp only [CollatzResearch.WordTrace]
  refine ⟨69427187482868741691307223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46284791655245827794204815 69427187482868741691307223)
  ·
    refine ⟨104140781224303112536960835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69427187482868741691307223 104140781224303112536960835)
    ·
      refine ⟨156211171836454668805441253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104140781224303112536960835 156211171836454668805441253)
      ·
        refine ⟨29289594719335250401020235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156211171836454668805441253 29289594719335250401020235)
        ·
          refine ⟨43934392079002875601530353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29289594719335250401020235 43934392079002875601530353)
          ·
            refine ⟨32950794059252156701147765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43934392079002875601530353 32950794059252156701147765)
            ·
              refine ⟨3089136943054889690732603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32950794059252156701147765 3089136943054889690732603)
              ·
                refine ⟨4633705414582334536098905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089136943054889690732603 4633705414582334536098905)
                ·
                  refine ⟨3475279060936750902074179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4633705414582334536098905 3475279060936750902074179)
                  ·
                    refine ⟨5212918591405126353111269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475279060936750902074179 5212918591405126353111269)
                    ·
                      refine ⟨977422235888461191208363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5212918591405126353111269 977422235888461191208363)
                      ·
                        rfl

theorem cell23_1903523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1903523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903523 prefixEnd_1903523 := by exact prefixLift 1903523
  have htrace : WordTrace (prefixWord ++ tailWord_1903523) baseStart_1903523 baseEnd_1903523 := by
    simpa [prefixWord, tailWord_1903523, baseEnd_1903523] using wordTrace_append hprefix tailTrace_1903523
  have hstable : (prefixWord ++ tailWord_1903523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903523).length < 2 ^ (prefixWord ++ tailWord_1903523).sum := by decide
  have hdescent : baseEnd_1903523 < baseStart_1903523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903543 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1903543 : Nat := 118140960795 + 1903543 * 2 ^ 59
def prefixEnd_1903543 : Nat := 4983230072969 + 3 ^ 40 * 1903543 * 2
def baseEnd_1903543 : Nat := 977432505501551112958271

theorem tailTrace_1903543 : CollatzResearch.WordTrace tailWord_1903543 prefixEnd_1903543 977432505501551112958271 := by
  unfold tailWord_1903543
  simp only [CollatzResearch.WordTrace]
  refine ⟨69427916942796285107035283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46285277961864190071356855 69427916942796285107035283)
  ·
    refine ⟨104141875414194427660552925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69427916942796285107035283 104141875414194427660552925)
    ·
      refine ⟨39053203280322910372707347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104141875414194427660552925 39053203280322910372707347)
      ·
        refine ⟨58579804920484365559061021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39053203280322910372707347 58579804920484365559061021)
        ·
          refine ⟨21967426845181637084647883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58579804920484365559061021 21967426845181637084647883)
          ·
            refine ⟨32951140267772455626971825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21967426845181637084647883 32951140267772455626971825)
            ·
              refine ⟨24713355200829341720228869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32951140267772455626971825 24713355200829341720228869)
              ·
                refine ⟨4633754100155501572542913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24713355200829341720228869 4633754100155501572542913)
                ·
                  refine ⟨3475315575116626179407185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4633754100155501572542913 3475315575116626179407185)
                  ·
                    refine ⟨2606486681337469634555389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3475315575116626179407185 2606486681337469634555389)
                    ·
                      refine ⟨977432505501551112958271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606486681337469634555389 977432505501551112958271)
                      ·
                        rfl

theorem cell23_1903543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1903543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903543 prefixEnd_1903543 := by exact prefixLift 1903543
  have htrace : WordTrace (prefixWord ++ tailWord_1903543) baseStart_1903543 baseEnd_1903543 := by
    simpa [prefixWord, tailWord_1903543, baseEnd_1903543] using wordTrace_append hprefix tailTrace_1903543
  have hstable : (prefixWord ++ tailWord_1903543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903543).length < 2 ^ (prefixWord ++ tailWord_1903543).sum := by decide
  have hdescent : baseEnd_1903543 < baseStart_1903543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903546 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_1903546 : Nat := 118140960795 + 1903546 * 2 ^ 59
def prefixEnd_1903546 : Nat := 4983230072969 + 3 ^ 40 * 1903546 * 2
def baseEnd_1903546 : Nat := 108603782882612733468973

theorem tailTrace_1903546 : CollatzResearch.WordTrace tailWord_1903546 prefixEnd_1903546 108603782882612733468973 := by
  unfold tailWord_1903546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17357006590446354154848623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46285350907856944412929661 17357006590446354154848623)
  ·
    refine ⟨26035509885669531232272935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17357006590446354154848623 26035509885669531232272935)
    ·
      refine ⟨39053264828504296848409403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26035509885669531232272935 39053264828504296848409403)
      ·
        refine ⟨58579897242756445272614105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39053264828504296848409403 58579897242756445272614105)
        ·
          refine ⟨43934922932067333954460579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58579897242756445272614105 43934922932067333954460579)
          ·
            refine ⟨65902384398101000931690869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43934922932067333954460579 65902384398101000931690869)
            ·
              refine ⟨6178348537321968837346019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65902384398101000931690869 6178348537321968837346019)
              ·
                refine ⟨9267522805982953256019029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178348537321968837346019 9267522805982953256019029)
                ·
                  refine ⟨108603782882612733468973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9267522805982953256019029 108603782882612733468973)
                  ·
                    rfl

theorem cell23_1903546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_1903546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903546 prefixEnd_1903546 := by exact prefixLift 1903546
  have htrace : WordTrace (prefixWord ++ tailWord_1903546) baseStart_1903546 baseEnd_1903546 := by
    simpa [prefixWord, tailWord_1903546, baseEnd_1903546] using wordTrace_append hprefix tailTrace_1903546
  have hstable : (prefixWord ++ tailWord_1903546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903546).length < 2 ^ (prefixWord ++ tailWord_1903546).sum := by decide
  have hdescent : baseEnd_1903546 < baseStart_1903546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903550 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1903550 : Nat := 118140960795 + 1903550 * 2 ^ 59
def prefixEnd_1903550 : Nat := 4983230072969 + 3 ^ 40 * 1903550 * 2
def baseEnd_1903550 : Nat := 325812033288710861856913

theorem tailTrace_1903550 : CollatzResearch.WordTrace tailWord_1903550 prefixEnd_1903550 325812033288710861856913 := by
  unfold tailWord_1903550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678521531721365662817513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46285448169180616868360069 8678521531721365662817513)
  ·
    refine ⟨6508891148791024247113135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8678521531721365662817513 6508891148791024247113135)
    ·
      refine ⟨9763336723186536370669703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508891148791024247113135 9763336723186536370669703)
      ·
        refine ⟨14645005084779804556004555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9763336723186536370669703 14645005084779804556004555)
        ·
          refine ⟨21967507627169706834006833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645005084779804556004555 21967507627169706834006833)
          ·
            refine ⟨16475630720377280125505125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21967507627169706834006833 16475630720377280125505125)
            ·
              refine ⟨3089180760070740023532211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16475630720377280125505125 3089180760070740023532211)
              ·
                refine ⟨4633771140106110035298317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089180760070740023532211 4633771140106110035298317)
                ·
                  refine ⟨1737664177539791263236869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4633771140106110035298317 1737664177539791263236869)
                  ·
                    refine ⟨325812033288710861856913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1737664177539791263236869 325812033288710861856913)
                    ·
                      rfl

theorem cell23_1903550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1903550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903550 prefixEnd_1903550 := by exact prefixLift 1903550
  have htrace : WordTrace (prefixWord ++ tailWord_1903550) baseStart_1903550 baseEnd_1903550 := by
    simpa [prefixWord, tailWord_1903550, baseEnd_1903550] using wordTrace_append hprefix tailTrace_1903550
  have hstable : (prefixWord ++ tailWord_1903550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903550).length < 2 ^ (prefixWord ++ tailWord_1903550).sum := by decide
  have hdescent : baseEnd_1903550 < baseStart_1903550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903613 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_1903613 : Nat := 118140960795 + 1903613 * 2 ^ 59
def prefixEnd_1903613 : Nat := 4983230072969 + 3 ^ 40 * 1903613 * 2
def baseEnd_1903613 : Nat := 977468449147365839082949

theorem tailTrace_1903613 : CollatzResearch.WordTrace tailWord_1903613 prefixEnd_1903613 977468449147365839082949 := by
  unfold tailWord_1903613
  simp only [CollatzResearch.WordTrace]
  refine ⟨69430470052542687062083493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46286980035028458041388995 69430470052542687062083493)
  ·
    refine ⟨13018213134851753824140655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69430470052542687062083493 13018213134851753824140655)
    ·
      refine ⟨19527319702277630736210983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13018213134851753824140655 19527319702277630736210983)
      ·
        refine ⟨29290979553416446104316475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19527319702277630736210983 29290979553416446104316475)
        ·
          refine ⟨43936469330124669156474713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29290979553416446104316475 43936469330124669156474713)
          ·
            refine ⟨32952351997593501867356035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43936469330124669156474713 32952351997593501867356035)
            ·
              refine ⟨49428527996390252801034053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32952351997593501867356035 49428527996390252801034053)
              ·
                refine ⟨9267848999323172400193885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49428527996390252801034053 9267848999323172400193885)
                ·
                  refine ⟨3475443374746189650072707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9267848999323172400193885 3475443374746189650072707)
                  ·
                    refine ⟨5213165062119284475109061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475443374746189650072707 5213165062119284475109061)
                    ·
                      refine ⟨977468449147365839082949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5213165062119284475109061 977468449147365839082949)
                      ·
                        rfl

theorem cell23_1903613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_1903613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903613 prefixEnd_1903613 := by exact prefixLift 1903613
  have htrace : WordTrace (prefixWord ++ tailWord_1903613) baseStart_1903613 baseEnd_1903613 := by
    simpa [prefixWord, tailWord_1903613, baseEnd_1903613] using wordTrace_append hprefix tailTrace_1903613
  have hstable : (prefixWord ++ tailWord_1903613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903613).length < 2 ^ (prefixWord ++ tailWord_1903613).sum := by decide
  have hdescent : baseEnd_1903613 < baseStart_1903613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903614 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1903614 : Nat := 118140960795 + 1903614 * 2 ^ 59
def prefixEnd_1903614 : Nat := 4983230072969 + 3 ^ 40 * 1903614 * 2
def baseEnd_1903614 : Nat := 108607662514224481685605

theorem tailTrace_1903614 : CollatzResearch.WordTrace tailWord_1903614 prefixEnd_1903614 108607662514224481685605 := by
  unfold tailWord_1903614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678813315692383029108737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46287004350359376155246597 8678813315692383029108737)
  ·
    refine ⟨6509109986769287271831553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8678813315692383029108737 6509109986769287271831553)
    ·
      refine ⟨4881832490076965453873665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6509109986769287271831553 4881832490076965453873665)
      ·
        refine ⟨3661374367557724090405249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4881832490076965453873665 3661374367557724090405249)
        ·
          refine ⟨2746030775668293067803937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3661374367557724090405249 2746030775668293067803937)
          ·
            refine ⟨2059523081751219800852953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746030775668293067803937 2059523081751219800852953)
            ·
              refine ⟨1544642311313414850639715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059523081751219800852953 1544642311313414850639715)
              ·
                refine ⟨2316963466970122275959573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544642311313414850639715 2316963466970122275959573)
                ·
                  refine ⟨108607662514224481685605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2316963466970122275959573 108607662514224481685605)
                  ·
                    rfl

theorem cell23_1903614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1903614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903614 prefixEnd_1903614 := by exact prefixLift 1903614
  have htrace : WordTrace (prefixWord ++ tailWord_1903614) baseStart_1903614 baseEnd_1903614 := by
    simpa [prefixWord, tailWord_1903614, baseEnd_1903614] using wordTrace_append hprefix tailTrace_1903614
  have hstable : (prefixWord ++ tailWord_1903614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903614).length < 2 ^ (prefixWord ++ tailWord_1903614).sum := by decide
  have hdescent : baseEnd_1903614 < baseStart_1903614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903616 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1903616 : Nat := 118140960795 + 1903616 * 2 ^ 59
def prefixEnd_1903616 : Nat := 4983230072969 + 3 ^ 40 * 1903616 * 2
def baseEnd_1903616 : Nat := 977469989589329327345435

theorem tailTrace_1903616 : CollatzResearch.WordTrace tailWord_1903616 prefixEnd_1903616 977469989589329327345435 := by
  unfold tailWord_1903616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34715289735765909287221351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46287052981021212382961801 34715289735765909287221351)
  ·
    refine ⟨52072934603648863930832027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34715289735765909287221351 52072934603648863930832027)
    ·
      refine ⟨78109401905473295896248041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52072934603648863930832027 78109401905473295896248041)
      ·
        refine ⟨58582051429104971922186031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78109401905473295896248041 58582051429104971922186031)
        ·
          refine ⟨87873077143657457883279047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58582051429104971922186031 87873077143657457883279047)
          ·
            refine ⟨131809615715486186824918571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87873077143657457883279047 131809615715486186824918571)
            ·
              refine ⟨197714423573229280237377857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131809615715486186824918571 197714423573229280237377857)
              ·
                refine ⟨148285817679921960178033393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197714423573229280237377857 148285817679921960178033393)
                ·
                  refine ⟨111214363259941470133525045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148285817679921960178033393 111214363259941470133525045)
                  ·
                    refine ⟨10426346555619512825017973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111214363259941470133525045 10426346555619512825017973)
                    ·
                      refine ⟨977469989589329327345435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10426346555619512825017973 977469989589329327345435)
                      ·
                        rfl

theorem cell23_1903616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1903616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903616 prefixEnd_1903616 := by exact prefixLift 1903616
  have htrace : WordTrace (prefixWord ++ tailWord_1903616) baseStart_1903616 baseEnd_1903616 := by
    simpa [prefixWord, tailWord_1903616, baseEnd_1903616] using wordTrace_append hprefix tailTrace_1903616
  have hstable : (prefixWord ++ tailWord_1903616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903616).length < 2 ^ (prefixWord ++ tailWord_1903616).sum := by decide
  have hdescent : baseEnd_1903616 < baseStart_1903616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903623 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1903623 : Nat := 118140960795 + 1903623 * 2 ^ 59
def prefixEnd_1903623 : Nat := 4983230072969 + 3 ^ 40 * 1903623 * 2
def baseEnd_1903623 : Nat := 325824527984636933319301

theorem tailTrace_1903623 : CollatzResearch.WordTrace tailWord_1903623 prefixEnd_1903623 325824527984636933319301 := by
  unfold tailWord_1903623
  simp only [CollatzResearch.WordTrace]
  refine ⟨69430834782506458769947523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46287223188337639179965015 69430834782506458769947523)
  ·
    refine ⟨104146252173759688154921285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69430834782506458769947523 104146252173759688154921285)
    ·
      refine ⟨19527422282579941529047741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104146252173759688154921285 19527422282579941529047741)
      ·
        refine ⟨7322783355967478073392903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19527422282579941529047741 7322783355967478073392903)
        ·
          refine ⟨10984175033951217110089355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7322783355967478073392903 10984175033951217110089355)
          ·
            refine ⟨16476262550926825665134033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10984175033951217110089355 16476262550926825665134033)
            ·
              refine ⟨12357196913195119248850525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16476262550926825665134033 12357196913195119248850525)
              ·
                refine ⟨4633948842448169718318947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12357196913195119248850525 4633948842448169718318947)
                ·
                  refine ⟨6950923263672254577478421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4633948842448169718318947 6950923263672254577478421)
                  ·
                    refine ⟨325824527984636933319301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6950923263672254577478421 325824527984636933319301)
                    ·
                      rfl

theorem cell23_1903623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1903623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903623 prefixEnd_1903623 := by exact prefixLift 1903623
  have htrace : WordTrace (prefixWord ++ tailWord_1903623) baseStart_1903623 baseEnd_1903623 := by
    simpa [prefixWord, tailWord_1903623, baseEnd_1903623] using wordTrace_append hprefix tailTrace_1903623
  have hstable : (prefixWord ++ tailWord_1903623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903623).length < 2 ^ (prefixWord ++ tailWord_1903623).sum := by decide
  have hdescent : baseEnd_1903623 < baseStart_1903623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903630 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1903630 : Nat := 118140960795 + 1903630 * 2 ^ 59
def prefixEnd_1903630 : Nat := 4983230072969 + 3 ^ 40 * 1903630 * 2
def baseEnd_1903630 : Nat := 977477178318492272570371

theorem tailTrace_1903630 : CollatzResearch.WordTrace tailWord_1903630 prefixEnd_1903630 977477178318492272570371 := by
  unfold tailWord_1903630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8678886261685137370681543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46287393395654065976968229 8678886261685137370681543)
  ·
    refine ⟨13018329392527706056022315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8678886261685137370681543 13018329392527706056022315)
    ·
      refine ⟨19527494088791559084033473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13018329392527706056022315 19527494088791559084033473)
      ·
        refine ⟨14645620566593669313025105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19527494088791559084033473 14645620566593669313025105)
        ·
          refine ⟨10984215424945251984768829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14645620566593669313025105 10984215424945251984768829)
          ·
            refine ⟨4119080784354469494288311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10984215424945251984768829 4119080784354469494288311)
            ·
              refine ⟨6178621176531704241432467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119080784354469494288311 6178621176531704241432467)
              ·
                refine ⟨9267931764797556362148701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6178621176531704241432467 9267931764797556362148701)
                ·
                  refine ⟨3475474411799083635805763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9267931764797556362148701 3475474411799083635805763)
                  ·
                    refine ⟨5213211617698625453708645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475474411799083635805763 5213211617698625453708645)
                    ·
                      refine ⟨977477178318492272570371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5213211617698625453708645 977477178318492272570371)
                      ·
                        rfl

theorem cell23_1903630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1903630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903630 prefixEnd_1903630 := by exact prefixLift 1903630
  have htrace : WordTrace (prefixWord ++ tailWord_1903630) baseStart_1903630 baseEnd_1903630 := by
    simpa [prefixWord, tailWord_1903630, baseEnd_1903630] using wordTrace_append hprefix tailTrace_1903630
  have hstable : (prefixWord ++ tailWord_1903630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903630).length < 2 ^ (prefixWord ++ tailWord_1903630).sum := by decide
  have hdescent : baseEnd_1903630 < baseStart_1903630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903647 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 1, 1, 4]
def baseStart_1903647 : Nat := 118140960795 + 1903647 * 2 ^ 59
def prefixEnd_1903647 : Nat := 4983230072969 + 3 ^ 40 * 1903647 * 2
def baseEnd_1903647 : Nat := 977485907489618706057793

theorem tailTrace_1903647 : CollatzResearch.WordTrace tailWord_1903647 prefixEnd_1903647 977485907489618706057793 := by
  unfold tailWord_1903647
  simp only [CollatzResearch.WordTrace]
  refine ⟨69431710134419510868821195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46287806756279673912547463 69431710134419510868821195)
  ·
    refine ⟨104147565201629266303231793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69431710134419510868821195 104147565201629266303231793)
    ·
      refine ⟨78110673901221949727423845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104147565201629266303231793 78110673901221949727423845)
      ·
        refine ⟨14645751356479115573891971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78110673901221949727423845 14645751356479115573891971)
        ·
          refine ⟨21968627034718673360837957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645751356479115573891971 21968627034718673360837957)
          ·
            refine ⟨4119117569009751255157117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21968627034718673360837957 4119117569009751255157117)
            ·
              refine ⟨1544669088378656720683919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4119117569009751255157117 1544669088378656720683919)
              ·
                refine ⟨2317003632567985081025879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544669088378656720683919 2317003632567985081025879)
                ·
                  refine ⟨3475505448851977621538819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317003632567985081025879 3475505448851977621538819)
                  ·
                    refine ⟨5213258173277966432308229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3475505448851977621538819 5213258173277966432308229)
                    ·
                      refine ⟨977485907489618706057793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5213258173277966432308229 977485907489618706057793)
                      ·
                        rfl

theorem cell23_1903647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_1903647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903647 prefixEnd_1903647 := by exact prefixLift 1903647
  have htrace : WordTrace (prefixWord ++ tailWord_1903647) baseStart_1903647 baseEnd_1903647 := by
    simpa [prefixWord, tailWord_1903647, baseEnd_1903647] using wordTrace_append hprefix tailTrace_1903647
  have hstable : (prefixWord ++ tailWord_1903647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903647).length < 2 ^ (prefixWord ++ tailWord_1903647).sum := by decide
  have hdescent : baseEnd_1903647 < baseStart_1903647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903650 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1903650 : Nat := 118140960795 + 1903650 * 2 ^ 59
def prefixEnd_1903650 : Nat := 4983230072969 + 3 ^ 40 * 1903650 * 2
def baseEnd_1903650 : Nat := 977487447931582194320279

theorem tailTrace_1903650 : CollatzResearch.WordTrace tailWord_1903650 prefixEnd_1903650 977487447931582194320279 := by
  unfold tailWord_1903650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17357954888352160595295101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46287879702272428254120269 17357954888352160595295101)
  ·
    refine ⟨6509233083132060223235663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17357954888352160595295101 6509233083132060223235663)
    ·
      refine ⟨9763849624698090334853495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509233083132060223235663 9763849624698090334853495)
      ·
        refine ⟨14645774437047135502280243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9763849624698090334853495 14645774437047135502280243)
        ·
          refine ⟨21968661655570703253420365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645774437047135502280243 21968661655570703253420365)
          ·
            refine ⟨8238248120839013720032637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21968661655570703253420365 8238248120839013720032637)
            ·
              refine ⟨3089343045314630145012239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8238248120839013720032637 3089343045314630145012239)
              ·
                refine ⟨4634014567971945217518359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089343045314630145012239 4634014567971945217518359)
                ·
                  refine ⟨6951021851957917826277539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634014567971945217518359 6951021851957917826277539)
                  ·
                    refine ⟨10426532777936876739416309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6951021851957917826277539 10426532777936876739416309)
                    ·
                      refine ⟨977487447931582194320279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10426532777936876739416309 977487447931582194320279)
                      ·
                        rfl

theorem cell23_1903650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1903650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903650 prefixEnd_1903650 := by exact prefixLift 1903650
  have htrace : WordTrace (prefixWord ++ tailWord_1903650) baseStart_1903650 baseEnd_1903650 := by
    simpa [prefixWord, tailWord_1903650, baseEnd_1903650] using wordTrace_append hprefix tailTrace_1903650
  have hstable : (prefixWord ++ tailWord_1903650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903650).length < 2 ^ (prefixWord ++ tailWord_1903650).sum := by decide
  have hdescent : baseEnd_1903650 < baseStart_1903650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903658 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1903658 : Nat := 118140960795 + 1903658 * 2 ^ 59
def prefixEnd_1903658 : Nat := 4983230072969 + 3 ^ 40 * 1903658 * 2
def baseEnd_1903658 : Nat := 977491555776818163020243

theorem tailTrace_1903658 : CollatzResearch.WordTrace tailWord_1903658 prefixEnd_1903658 977491555776818163020243 := by
  unfold tailWord_1903658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17358027834344914936867907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46288074224919773164981085 17358027834344914936867907)
  ·
    refine ⟨26037041751517372405301861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17358027834344914936867907 26037041751517372405301861)
    ·
      refine ⟨4881945328409507325994099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26037041751517372405301861 4881945328409507325994099)
      ·
        refine ⟨7322917992614260988991149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4881945328409507325994099 7322917992614260988991149)
        ·
          refine ⟨2746094247230347870871681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7322917992614260988991149 2746094247230347870871681)
          ·
            refine ⟨2059570685422760903153761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2746094247230347870871681 2059570685422760903153761)
            ·
              refine ⟨1544678014067070677365321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2059570685422760903153761 1544678014067070677365321)
              ·
                refine ⟨1158508510550303008023991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544678014067070677365321 1158508510550303008023991)
                ·
                  refine ⟨1737762765825454512035987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158508510550303008023991 1737762765825454512035987)
                  ·
                    refine ⟨2606644148738181768053981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1737762765825454512035987 2606644148738181768053981)
                    ·
                      refine ⟨977491555776818163020243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2606644148738181768053981 977491555776818163020243)
                      ·
                        rfl

theorem cell23_1903658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1903658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903658 prefixEnd_1903658 := by exact prefixLift 1903658
  have htrace : WordTrace (prefixWord ++ tailWord_1903658) baseStart_1903658 baseEnd_1903658 := by
    simpa [prefixWord, tailWord_1903658, baseEnd_1903658] using wordTrace_append hprefix tailTrace_1903658
  have hstable : (prefixWord ++ tailWord_1903658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903658).length < 2 ^ (prefixWord ++ tailWord_1903658).sum := by decide
  have hdescent : baseEnd_1903658 < baseStart_1903658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1903664 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 1, 2, 2]
def baseStart_1903664 : Nat := 118140960795 + 1903664 * 2 ^ 59
def prefixEnd_1903664 : Nat := 4983230072969 + 3 ^ 40 * 1903664 * 2
def baseEnd_1903664 : Nat := 977494636660745139545215

theorem tailTrace_1903664 : CollatzResearch.WordTrace tailWord_1903664 prefixEnd_1903664 977494636660745139545215 := by
  unfold tailWord_1903664
  simp only [CollatzResearch.WordTrace]
  refine ⟨34716165087678961386095023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46288220116905281848126697 34716165087678961386095023)
  ·
    refine ⟨52074247631518442079142535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34716165087678961386095023 52074247631518442079142535)
    ·
      refine ⟨78111371447277663118713803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52074247631518442079142535 78111371447277663118713803)
      ·
        refine ⟨117167057170916494678070705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78111371447277663118713803 117167057170916494678070705)
        ·
          refine ⟨87875292878187371008553029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117167057170916494678070705 87875292878187371008553029)
          ·
            refine ⟨16476617414660132064103693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87875292878187371008553029 16476617414660132064103693)
            ·
              refine ⟨6178731530497549524038885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16476617414660132064103693 6178731530497549524038885)
              ·
                refine ⟨1158512161968290535757291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6178731530497549524038885 1158512161968290535757291)
                ·
                  refine ⟨1737768242952435803635937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158512161968290535757291 1737768242952435803635937)
                  ·
                    refine ⟨1303326182214326852726953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1737768242952435803635937 1303326182214326852726953)
                    ·
                      refine ⟨977494636660745139545215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1303326182214326852726953 977494636660745139545215)
                      ·
                        rfl

theorem cell23_1903664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 1, 2, 2].length) (baseStart_1903664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1903664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1903664 prefixEnd_1903664 := by exact prefixLift 1903664
  have htrace : WordTrace (prefixWord ++ tailWord_1903664) baseStart_1903664 baseEnd_1903664 := by
    simpa [prefixWord, tailWord_1903664, baseEnd_1903664] using wordTrace_append hprefix tailTrace_1903664
  have hstable : (prefixWord ++ tailWord_1903664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1903664).length < 2 ^ (prefixWord ++ tailWord_1903664).sum := by decide
  have hdescent : baseEnd_1903664 < baseStart_1903664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1903664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
