import V185TrunkScan22Chunk076

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_691949 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_691949 : Nat := 118140960795 + 691949 * 2 ^ 59
def prefixEnd_691949 : Nat := 4983230072969 + 3 ^ 40 * 691949 * 2
def baseEnd_691949 : Nat := 236868283598678986703527

theorem tailTrace_691949 : CollatzResearch.WordTrace tailWord_691949 prefixEnd_691949 236868283598678986703527 := by
  unfold tailWord_691949
  simp only [CollatzResearch.WordTrace]
  refine ⟨25237453370194423325878901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16824968913462948883919267 25237453370194423325878901)
  ·
    refine ⟨2366011253455727186801147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25237453370194423325878901 2366011253455727186801147)
    ·
      refine ⟨3549016880183590780201721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366011253455727186801147 3549016880183590780201721)
      ·
        refine ⟨2661762660137693085151291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3549016880183590780201721 2661762660137693085151291)
        ·
          refine ⟨3992643990206539627726937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661762660137693085151291 3992643990206539627726937)
          ·
            refine ⟨2994482992654904720795203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992643990206539627726937 2994482992654904720795203)
            ·
              refine ⟨4491724488982357081192805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994482992654904720795203 4491724488982357081192805)
              ·
                refine ⟨842198341684191952723651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4491724488982357081192805 842198341684191952723651)
                ·
                  refine ⟨1263297512526287929085477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842198341684191952723651 1263297512526287929085477)
                  ·
                    refine ⟨236868283598678986703527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263297512526287929085477 236868283598678986703527)
                    ·
                      rfl

theorem cell22_691949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_691949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691949 prefixEnd_691949 := by exact prefixLift 691949
  have htrace : WordTrace (prefixWord ++ tailWord_691949) baseStart_691949 baseEnd_691949 := by
    simpa [prefixWord, tailWord_691949, baseEnd_691949] using wordTrace_append hprefix tailTrace_691949
  have hstable : (prefixWord ++ tailWord_691949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691949).length < 2 ^ (prefixWord ++ tailWord_691949).sum := by decide
  have hdescent : baseEnd_691949 < baseStart_691949 := by decide
  rcases family_descends (prefixWord ++ tailWord_691949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691974 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_691974 : Nat := 118140960795 + 691974 * 2 ^ 59
def prefixEnd_691974 : Nat := 4983230072969 + 3 ^ 40 * 691974 * 2
def baseEnd_691974 : Nat := 236876841609587254828451

theorem tailTrace_691974 : CollatzResearch.WordTrace tailWord_691974 prefixEnd_691974 236876841609587254828451 := by
  unfold tailWord_691974
  simp only [CollatzResearch.WordTrace]
  refine ⟨788698912346995393610593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16825576796735901730359317 788698912346995393610593)
  ·
    refine ⟨591524184260246545207945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 788698912346995393610593 591524184260246545207945)
    ·
      refine ⟨443643138195184908905959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591524184260246545207945 443643138195184908905959)
      ·
        refine ⟨665464707292777363358939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443643138195184908905959 665464707292777363358939)
        ·
          refine ⟨998197060939166045038409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665464707292777363358939 998197060939166045038409)
          ·
            refine ⟨748647795704374533778807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998197060939166045038409 748647795704374533778807)
            ·
              refine ⟨1122971693556561800668211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748647795704374533778807 1122971693556561800668211)
              ·
                refine ⟨1684457540334842701002317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122971693556561800668211 1684457540334842701002317)
                ·
                  refine ⟨631671577625566012875869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1684457540334842701002317 631671577625566012875869)
                  ·
                    refine ⟨236876841609587254828451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631671577625566012875869 236876841609587254828451)
                    ·
                      rfl

theorem cell22_691974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_691974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_691974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_691974 prefixEnd_691974 := by exact prefixLift 691974
  have htrace : WordTrace (prefixWord ++ tailWord_691974) baseStart_691974 baseEnd_691974 := by
    simpa [prefixWord, tailWord_691974, baseEnd_691974] using wordTrace_append hprefix tailTrace_691974
  have hstable : (prefixWord ++ tailWord_691974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691974).length < 2 ^ (prefixWord ++ tailWord_691974).sum := by decide
  have hdescent : baseEnd_691974 < baseStart_691974 := by decide
  rcases family_descends (prefixWord ++ tailWord_691974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692041 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 1, 3]
def baseStart_692041 : Nat := 118140960795 + 692041 * 2 ^ 59
def prefixEnd_692041 : Nat := 4983230072969 + 3 ^ 40 * 692041 * 2
def baseEnd_692041 : Nat := 236899777078821413403245

theorem tailTrace_692041 : CollatzResearch.WordTrace tailWord_692041 prefixEnd_692041 236899777078821413403245 := by
  unfold tailWord_692041
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240808885861123038227977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16827205923907415358818651 25240808885861123038227977)
  ·
    refine ⟨18930606664395842278670983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25240808885861123038227977 18930606664395842278670983)
    ·
      refine ⟨28395909996593763418006475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18930606664395842278670983 28395909996593763418006475)
      ·
        refine ⟨42593864994890645127009713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28395909996593763418006475 42593864994890645127009713)
        ·
          refine ⟨31945398746167983845257285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42593864994890645127009713 31945398746167983845257285)
          ·
            refine ⟨5989762264906496970985741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31945398746167983845257285 5989762264906496970985741)
            ·
              refine ⟨2246160849339936364119653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5989762264906496970985741 2246160849339936364119653)
              ·
                refine ⟨421155159251238068272435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2246160849339936364119653 421155159251238068272435)
                ·
                  refine ⟨631732738876857102408653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421155159251238068272435 631732738876857102408653)
                  ·
                    refine ⟨236899777078821413403245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631732738876857102408653 236899777078821413403245)
                    ·
                      rfl

theorem cell22_692041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 3].length) (baseStart_692041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692041 prefixEnd_692041 := by exact prefixLift 692041
  have htrace : WordTrace (prefixWord ++ tailWord_692041) baseStart_692041 baseEnd_692041 := by
    simpa [prefixWord, tailWord_692041, baseEnd_692041] using wordTrace_append hprefix tailTrace_692041
  have hstable : (prefixWord ++ tailWord_692041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692041).length < 2 ^ (prefixWord ++ tailWord_692041).sum := by decide
  have hdescent : baseEnd_692041 < baseStart_692041 := by decide
  rcases family_descends (prefixWord ++ tailWord_692041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692082 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_692082 : Nat := 118140960795 + 692082 * 2 ^ 59
def prefixEnd_692082 : Nat := 4983230072969 + 3 ^ 40 * 692082 * 2
def baseEnd_692082 : Nat := 78971270738903657709373

theorem tailTrace_692082 : CollatzResearch.WordTrace tailWord_692082 prefixEnd_692082 78971270738903657709373 := by
  unfold tailWord_692082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6310576069678146760117625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16828202852475058026980333 6310576069678146760117625)
  ·
    refine ⟨4732932052258610070088219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6310576069678146760117625 4732932052258610070088219)
    ·
      refine ⟨7099398078387915105132329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4732932052258610070088219 7099398078387915105132329)
      ·
        refine ⟨5324548558790936328849247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7099398078387915105132329 5324548558790936328849247)
        ·
          refine ⟨7986822838186404493273871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324548558790936328849247 7986822838186404493273871)
          ·
            refine ⟨11980234257279606739910807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986822838186404493273871 11980234257279606739910807)
            ·
              refine ⟨17970351385919410109866211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11980234257279606739910807 17970351385919410109866211)
              ·
                refine ⟨26955527078879115164799317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17970351385919410109866211 26955527078879115164799317)
                ·
                  refine ⟨78971270738903657709373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26955527078879115164799317 78971270738903657709373)
                  ·
                    rfl

theorem cell22_692082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_692082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692082 prefixEnd_692082 := by exact prefixLift 692082
  have htrace : WordTrace (prefixWord ++ tailWord_692082) baseStart_692082 baseEnd_692082 := by
    simpa [prefixWord, tailWord_692082, baseEnd_692082] using wordTrace_append hprefix tailTrace_692082
  have hstable : (prefixWord ++ tailWord_692082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692082).length < 2 ^ (prefixWord ++ tailWord_692082).sum := by decide
  have hdescent : baseEnd_692082 < baseStart_692082 := by decide
  rcases family_descends (prefixWord ++ tailWord_692082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692099 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 6]
def baseStart_692099 : Nat := 118140960795 + 692099 * 2 ^ 59
def prefixEnd_692099 : Nat := 4983230072969 + 3 ^ 40 * 692099 * 2
def baseEnd_692099 : Nat := 78973210554709531817689

theorem tailTrace_692099 : CollatzResearch.WordTrace tailWord_692099 prefixEnd_692099 78973210554709531817689 := by
  unfold tailWord_692099
  simp only [CollatzResearch.WordTrace]
  refine ⟨25242924319650998943839351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16828616213100665962559567 25242924319650998943839351)
  ·
    refine ⟨37864386479476498415759027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25242924319650998943839351 37864386479476498415759027)
    ·
      refine ⟨56796579719214747623638541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37864386479476498415759027 56796579719214747623638541)
      ·
        refine ⟨21298717394705530358864453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56796579719214747623638541 21298717394705530358864453)
        ·
          refine ⟨3993509511507286942287085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21298717394705530358864453 3993509511507286942287085)
          ·
            refine ⟨1497566066815232603357657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3993509511507286942287085 1497566066815232603357657)
            ·
              refine ⟨1123174550111424452518243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497566066815232603357657 1123174550111424452518243)
              ·
                refine ⟨1684761825167136678777365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123174550111424452518243 1684761825167136678777365)
                ·
                  refine ⟨78973210554709531817689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1684761825167136678777365 78973210554709531817689)
                  ·
                    rfl

theorem cell22_692099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 6].length) (baseStart_692099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692099 prefixEnd_692099 := by exact prefixLift 692099
  have htrace : WordTrace (prefixWord ++ tailWord_692099) baseStart_692099 baseEnd_692099 := by
    simpa [prefixWord, tailWord_692099, baseEnd_692099] using wordTrace_append hprefix tailTrace_692099
  have hstable : (prefixWord ++ tailWord_692099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692099).length < 2 ^ (prefixWord ++ tailWord_692099).sum := by decide
  have hdescent : baseEnd_692099 < baseStart_692099 := by decide
  rcases family_descends (prefixWord ++ tailWord_692099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692112 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_692112 : Nat := 118140960795 + 692112 * 2 ^ 59
def prefixEnd_692112 : Nat := 4983230072969 + 3 ^ 40 * 692112 * 2
def baseEnd_692112 : Nat := 236924081829800894878027

theorem tailTrace_692112 : CollatzResearch.WordTrace tailWord_692112 prefixEnd_692112 236924081829800894878027 := by
  unfold tailWord_692112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12621699234301951082031295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16828932312402601442708393 12621699234301951082031295)
  ·
    refine ⟨18932548851452926623046943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12621699234301951082031295 18932548851452926623046943)
    ·
      refine ⟨28398823277179389934570415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18932548851452926623046943 28398823277179389934570415)
      ·
        refine ⟨42598234915769084901855623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28398823277179389934570415 42598234915769084901855623)
        ·
          refine ⟨63897352373653627352783435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42598234915769084901855623 63897352373653627352783435)
          ·
            refine ⟨95846028560480441029175153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63897352373653627352783435 95846028560480441029175153)
            ·
              refine ⟨71884521420360330771881365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95846028560480441029175153 71884521420360330771881365)
              ·
                refine ⟨3369586941579390504931939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71884521420360330771881365 3369586941579390504931939)
                ·
                  refine ⟨5054380412369085757397909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369586941579390504931939 5054380412369085757397909)
                  ·
                    refine ⟨236924081829800894878027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5054380412369085757397909 236924081829800894878027)
                    ·
                      rfl

theorem cell22_692112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_692112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692112 prefixEnd_692112 := by exact prefixLift 692112
  have htrace : WordTrace (prefixWord ++ tailWord_692112) baseStart_692112 baseEnd_692112 := by
    simpa [prefixWord, tailWord_692112, baseEnd_692112] using wordTrace_append hprefix tailTrace_692112
  have hstable : (prefixWord ++ tailWord_692112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692112).length < 2 ^ (prefixWord ++ tailWord_692112).sum := by decide
  have hdescent : baseEnd_692112 < baseStart_692112 := by decide
  rcases family_descends (prefixWord ++ tailWord_692112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692206 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_692206 : Nat := 118140960795 + 692206 * 2 ^ 59
def prefixEnd_692206 : Nat := 4983230072969 + 3 ^ 40 * 692206 * 2
def baseEnd_692206 : Nat := 78985419983605327675913

theorem tailTrace_692206 : CollatzResearch.WordTrace tailWord_692206 prefixEnd_692206 78985419983605327675913 := by
  unfold tailWord_692206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155853366282919527248059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16831217953508904145322981 3155853366282919527248059)
  ·
    refine ⟨4733780049424379290872089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3155853366282919527248059 4733780049424379290872089)
    ·
      refine ⟨3550335037068284468154067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4733780049424379290872089 3550335037068284468154067)
      ·
        refine ⟨5325502555602426702231101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550335037068284468154067 5325502555602426702231101)
        ·
          refine ⟨1997063458350910013336663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5325502555602426702231101 1997063458350910013336663)
          ·
            refine ⟨2995595187526365020004995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997063458350910013336663 2995595187526365020004995)
            ·
              refine ⟨4493392781289547530007493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995595187526365020004995 4493392781289547530007493)
              ·
                refine ⟨842511146491790161876405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4493392781289547530007493 842511146491790161876405)
                ·
                  refine ⟨78985419983605327675913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842511146491790161876405 78985419983605327675913)
                  ·
                    rfl

theorem cell22_692206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_692206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692206 prefixEnd_692206 := by exact prefixLift 692206
  have htrace : WordTrace (prefixWord ++ tailWord_692206) baseStart_692206 baseEnd_692206 := by
    simpa [prefixWord, tailWord_692206, baseEnd_692206] using wordTrace_append hprefix tailTrace_692206
  have hstable : (prefixWord ++ tailWord_692206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692206).length < 2 ^ (prefixWord ++ tailWord_692206).sum := by decide
  have hdescent : baseEnd_692206 < baseStart_692206 := by decide
  rcases family_descends (prefixWord ++ tailWord_692206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692219 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 3, 4]
def baseStart_692219 : Nat := 118140960795 + 692219 * 2 ^ 59
def prefixEnd_692219 : Nat := 4983230072969 + 3 ^ 40 * 692219 * 2
def baseEnd_692219 : Nat := 236960710116488282452699

theorem tailTrace_692219 : CollatzResearch.WordTrace tailWord_692219 prefixEnd_692219 236960710116488282452699 := by
  unfold tailWord_692219
  simp only [CollatzResearch.WordTrace]
  refine ⟨25247301079216259438207711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16831534052810839625471807 25247301079216259438207711)
  ·
    refine ⟨37870951618824389157311567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25247301079216259438207711 37870951618824389157311567)
    ·
      refine ⟨56806427428236583735967351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37870951618824389157311567 56806427428236583735967351)
      ·
        refine ⟨85209641142354875603951027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56806427428236583735967351 85209641142354875603951027)
        ·
          refine ⟨127814461713532313405926541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85209641142354875603951027 127814461713532313405926541)
          ·
            refine ⟨47930423142574617527222453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127814461713532313405926541 47930423142574617527222453)
            ·
              refine ⟨4493477169616370393177105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47930423142574617527222453 4493477169616370393177105)
              ·
                refine ⟨3370107877212277794882829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493477169616370393177105 3370107877212277794882829)
                ·
                  refine ⟨1263790453954604173081061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3370107877212277794882829 1263790453954604173081061)
                  ·
                    refine ⟨236960710116488282452699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263790453954604173081061 236960710116488282452699)
                    ·
                      rfl

theorem cell22_692219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_692219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692219 prefixEnd_692219 := by exact prefixLift 692219
  have htrace : WordTrace (prefixWord ++ tailWord_692219) baseStart_692219 baseEnd_692219 := by
    simpa [prefixWord, tailWord_692219, baseEnd_692219] using wordTrace_append hprefix tailTrace_692219
  have hstable : (prefixWord ++ tailWord_692219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692219).length < 2 ^ (prefixWord ++ tailWord_692219).sum := by decide
  have hdescent : baseEnd_692219 < baseStart_692219 := by decide
  rcases family_descends (prefixWord ++ tailWord_692219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692236 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_692236 : Nat := 118140960795 + 692236 * 2 ^ 59
def prefixEnd_692236 : Nat := 4983230072969 + 3 ^ 40 * 692236 * 2
def baseEnd_692236 : Nat := 236966529563905904777647

theorem tailTrace_692236 : CollatzResearch.WordTrace tailWord_692236 prefixEnd_692236 236966529563905904777647 := by
  unfold tailWord_692236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623960560077335670788281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16831947413436447561051041 12623960560077335670788281)
  ·
    refine ⟨9467970420058001753091211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12623960560077335670788281 9467970420058001753091211)
    ·
      refine ⟨14201955630087002629636817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9467970420058001753091211 14201955630087002629636817)
      ·
        refine ⟨10651466722565251972227613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14201955630087002629636817 10651466722565251972227613)
        ·
          refine ⟨3994300020961969489585355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10651466722565251972227613 3994300020961969489585355)
          ·
            refine ⟨5991450031442954234378033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994300020961969489585355 5991450031442954234378033)
            ·
              refine ⟨4493587523582215675783525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991450031442954234378033 4493587523582215675783525)
              ·
                refine ⟨842547660671665439209411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4493587523582215675783525 842547660671665439209411)
                ·
                  refine ⟨1263821491007498158814117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842547660671665439209411 1263821491007498158814117)
                  ·
                    refine ⟨236966529563905904777647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263821491007498158814117 236966529563905904777647)
                    ·
                      rfl

theorem cell22_692236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_692236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692236 prefixEnd_692236 := by exact prefixLift 692236
  have htrace : WordTrace (prefixWord ++ tailWord_692236) baseStart_692236 baseEnd_692236 := by
    simpa [prefixWord, tailWord_692236, baseEnd_692236] using wordTrace_append hprefix tailTrace_692236
  have hstable : (prefixWord ++ tailWord_692236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692236).length < 2 ^ (prefixWord ++ tailWord_692236).sum := by decide
  have hdescent : baseEnd_692236 < baseStart_692236 := by decide
  rcases family_descends (prefixWord ++ tailWord_692236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692244 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_692244 : Nat := 118140960795 + 692244 * 2 ^ 59
def prefixEnd_692244 : Nat := 4983230072969 + 3 ^ 40 * 692244 * 2
def baseEnd_692244 : Nat := 236969268127396550577623

theorem tailTrace_692244 : CollatzResearch.WordTrace tailWord_692244 prefixEnd_692244 236969268127396550577623 := by
  unfold tailWord_692244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624106452062844353933893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16832141936083792471911857 12624106452062844353933893)
  ·
    refine ⟨2367019959761783316362605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12624106452062844353933893 2367019959761783316362605)
    ·
      refine ⟨887632484910668743635977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2367019959761783316362605 887632484910668743635977)
      ·
        refine ⟨665724363683001557726983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887632484910668743635977 665724363683001557726983)
        ·
          refine ⟨998586545524502336590475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665724363683001557726983 998586545524502336590475)
          ·
            refine ⟨1497879818286753504885713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998586545524502336590475 1497879818286753504885713)
            ·
              refine ⟨1123409863715065128664285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497879818286753504885713 1123409863715065128664285)
              ·
                refine ⟨421278698893149423249107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1123409863715065128664285 421278698893149423249107)
                ·
                  refine ⟨631918048339724134873661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421278698893149423249107 631918048339724134873661)
                  ·
                    refine ⟨236969268127396550577623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631918048339724134873661 236969268127396550577623)
                    ·
                      rfl

theorem cell22_692244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_692244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692244 prefixEnd_692244 := by exact prefixLift 692244
  have htrace : WordTrace (prefixWord ++ tailWord_692244) baseStart_692244 baseEnd_692244 := by
    simpa [prefixWord, tailWord_692244, baseEnd_692244] using wordTrace_append hprefix tailTrace_692244
  have hstable : (prefixWord ++ tailWord_692244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692244).length < 2 ^ (prefixWord ++ tailWord_692244).sum := by decide
  have hdescent : baseEnd_692244 < baseStart_692244 := by decide
  rcases family_descends (prefixWord ++ tailWord_692244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692253 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_692253 : Nat := 118140960795 + 692253 * 2 ^ 59
def prefixEnd_692253 : Nat := 4983230072969 + 3 ^ 40 * 692253 * 2
def baseEnd_692253 : Nat := 236972349011323527102595

theorem tailTrace_692253 : CollatzResearch.WordTrace tailWord_692253 prefixEnd_692253 236972349011323527102595 := by
  unfold tailWord_692253
  simp only [CollatzResearch.WordTrace]
  refine ⟨25248541161093083244945413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16832360774062055496630275 25248541161093083244945413)
  ·
    refine ⟨4734101467704953108427265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25248541161093083244945413 4734101467704953108427265)
    ·
      refine ⟨3550576100778714831320449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4734101467704953108427265 3550576100778714831320449)
      ·
        refine ⟨2662932075584036123490337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3550576100778714831320449 2662932075584036123490337)
        ·
          refine ⟨1997199056688027092617753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662932075584036123490337 1997199056688027092617753)
          ·
            refine ⟨1497899292516020319463315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1997199056688027092617753 1497899292516020319463315)
            ·
              refine ⟨2246848938774030479194973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497899292516020319463315 2246848938774030479194973)
              ·
                refine ⟨842568352040261429698115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2246848938774030479194973 842568352040261429698115)
                ·
                  refine ⟨1263852528060392144547173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842568352040261429698115 1263852528060392144547173)
                  ·
                    refine ⟨236972349011323527102595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263852528060392144547173 236972349011323527102595)
                    ·
                      rfl

theorem cell22_692253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_692253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692253 prefixEnd_692253 := by exact prefixLift 692253
  have htrace : WordTrace (prefixWord ++ tailWord_692253) baseStart_692253 baseEnd_692253 := by
    simpa [prefixWord, tailWord_692253, baseEnd_692253] using wordTrace_append hprefix tailTrace_692253
  have hstable : (prefixWord ++ tailWord_692253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692253).length < 2 ^ (prefixWord ++ tailWord_692253).sum := by decide
  have hdescent : baseEnd_692253 < baseStart_692253 := by decide
  rcases family_descends (prefixWord ++ tailWord_692253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692311 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 5, 3]
def baseStart_692311 : Nat := 118140960795 + 692311 * 2 ^ 59
def prefixEnd_692311 : Nat := 4983230072969 + 3 ^ 40 * 692311 * 2
def baseEnd_692311 : Nat := 236992203596630709152417

theorem tailTrace_692311 : CollatzResearch.WordTrace tailWord_692311 prefixEnd_692311 236992203596630709152417 := by
  unfold tailWord_692311
  simp only [CollatzResearch.WordTrace]
  refine ⟨25250656594882959150556787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16833771063255306100371191 25250656594882959150556787)
  ·
    refine ⟨37875984892324438725835181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25250656594882959150556787 37875984892324438725835181)
    ·
      refine ⟨14203494334621664522188193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37875984892324438725835181 14203494334621664522188193)
      ·
        refine ⟨10652620750966248391641145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14203494334621664522188193 10652620750966248391641145)
        ·
          refine ⟨7989465563224686293730859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10652620750966248391641145 7989465563224686293730859)
          ·
            refine ⟨11984198344837029440596289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989465563224686293730859 11984198344837029440596289)
            ·
              refine ⟨8988148758627772080447217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11984198344837029440596289 8988148758627772080447217)
              ·
                refine ⟨6741111568970829060335413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8988148758627772080447217 6741111568970829060335413)
                ·
                  refine ⟨631979209591015224406445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6741111568970829060335413 631979209591015224406445)
                  ·
                    refine ⟨236992203596630709152417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631979209591015224406445 236992203596630709152417)
                    ·
                      rfl

theorem cell22_692311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_692311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692311 prefixEnd_692311 := by exact prefixLift 692311
  have htrace : WordTrace (prefixWord ++ tailWord_692311) baseStart_692311 baseEnd_692311 := by
    simpa [prefixWord, tailWord_692311, baseEnd_692311] using wordTrace_append hprefix tailTrace_692311
  have hstable : (prefixWord ++ tailWord_692311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692311).length < 2 ^ (prefixWord ++ tailWord_692311).sum := by decide
  have hdescent : baseEnd_692311 < baseStart_692311 := by decide
  rcases family_descends (prefixWord ++ tailWord_692311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692420 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 4]
def baseStart_692420 : Nat := 118140960795 + 692420 * 2 ^ 59
def prefixEnd_692420 : Nat := 4983230072969 + 3 ^ 40 * 692420 * 2
def baseEnd_692420 : Nat := 79009838841396919392361

theorem tailTrace_692420 : CollatzResearch.WordTrace tailWord_692420 prefixEnd_692420 79009838841396919392361 := by
  unfold tailWord_692420
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627316075744035383137357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16836421434325380510849809 12627316075744035383137357)
  ·
    refine ⟨4735243528404013268676509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12627316075744035383137357 4735243528404013268676509)
    ·
      refine ⟨1775716323151504975753691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4735243528404013268676509 1775716323151504975753691)
      ·
        refine ⟨2663574484727257463630537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775716323151504975753691 2663574484727257463630537)
        ·
          refine ⟨1997680863545443097722903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2663574484727257463630537 1997680863545443097722903)
          ·
            refine ⟨2996521295318164646584355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997680863545443097722903 2996521295318164646584355)
            ·
              refine ⟨4494781942977246969876533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996521295318164646584355 4494781942977246969876533)
              ·
                refine ⟨421385807154116903425925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4494781942977246969876533 421385807154116903425925)
                ·
                  refine ⟨79009838841396919392361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421385807154116903425925 79009838841396919392361)
                  ·
                    rfl

theorem cell22_692420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_692420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692420 prefixEnd_692420 := by exact prefixLift 692420
  have htrace : WordTrace (prefixWord ++ tailWord_692420) baseStart_692420 baseEnd_692420 := by
    simpa [prefixWord, tailWord_692420, baseEnd_692420] using wordTrace_append hprefix tailTrace_692420
  have hstable : (prefixWord ++ tailWord_692420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692420).length < 2 ^ (prefixWord ++ tailWord_692420).sum := by decide
  have hdescent : baseEnd_692420 < baseStart_692420 := by decide
  rcases family_descends (prefixWord ++ tailWord_692420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692548 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_692548 : Nat := 118140960795 + 692548 * 2 ^ 59
def prefixEnd_692548 : Nat := 4983230072969 + 3 ^ 40 * 692548 * 2
def baseEnd_692548 : Nat := 237073333540041090976691

theorem tailTrace_692548 : CollatzResearch.WordTrace tailWord_692548 prefixEnd_692548 237073333540041090976691 := by
  unfold tailWord_692548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629650347512174313467149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16839533796682899084622865 12629650347512174313467149)
  ·
    refine ⟨4736118880317065367550181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12629650347512174313467149 4736118880317065367550181)
    ·
      refine ⟨888022290059449756415659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4736118880317065367550181 888022290059449756415659)
      ·
        refine ⟨1332033435089174634623489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888022290059449756415659 1332033435089174634623489)
        ·
          refine ⟨999025076316880975967617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332033435089174634623489 999025076316880975967617)
          ·
            refine ⟨749268807237660731975713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999025076316880975967617 749268807237660731975713)
            ·
              refine ⟨561951605428245548981785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749268807237660731975713 561951605428245548981785)
              ·
                refine ⟨421463704071184161736339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561951605428245548981785 421463704071184161736339)
                ·
                  refine ⟨632195556106776242604509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421463704071184161736339 632195556106776242604509)
                  ·
                    refine ⟨237073333540041090976691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632195556106776242604509 237073333540041090976691)
                    ·
                      rfl

theorem cell22_692548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_692548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692548 prefixEnd_692548 := by exact prefixLift 692548
  have htrace : WordTrace (prefixWord ++ tailWord_692548) baseStart_692548 baseEnd_692548 := by
    simpa [prefixWord, tailWord_692548, baseEnd_692548] using wordTrace_append hprefix tailTrace_692548
  have hstable : (prefixWord ++ tailWord_692548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692548).length < 2 ^ (prefixWord ++ tailWord_692548).sum := by decide
  have hdescent : baseEnd_692548 < baseStart_692548 := by decide
  rcases family_descends (prefixWord ++ tailWord_692548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692572 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_692572 : Nat := 118140960795 + 692572 * 2 ^ 59
def prefixEnd_692572 : Nat := 4983230072969 + 3 ^ 40 * 692572 * 2
def baseEnd_692572 : Nat := 79027183076837676125539

theorem tailTrace_692572 : CollatzResearch.WordTrace tailWord_692572 prefixEnd_692572 79027183076837676125539 := by
  unfold tailWord_692572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630088023468700362903985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16840117364624933817205313 12630088023468700362903985)
  ·
    refine ⟨9472566017601525272177989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12630088023468700362903985 9472566017601525272177989)
    ·
      refine ⟨1776106128300285988533373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9472566017601525272177989 1776106128300285988533373)
      ·
        refine ⟨666039798112607245700015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1776106128300285988533373 666039798112607245700015)
        ·
          refine ⟨999059697168910868550023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666039798112607245700015 999059697168910868550023)
          ·
            refine ⟨1498589545753366302825035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999059697168910868550023 1498589545753366302825035)
            ·
              refine ⟨2247884318630049454237553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498589545753366302825035 2247884318630049454237553)
              ·
                refine ⟨1685913238972537090678165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247884318630049454237553 1685913238972537090678165)
                ·
                  refine ⟨79027183076837676125539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1685913238972537090678165 79027183076837676125539)
                  ·
                    rfl

theorem cell22_692572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_692572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692572 prefixEnd_692572 := by exact prefixLift 692572
  have htrace : WordTrace (prefixWord ++ tailWord_692572) baseStart_692572 baseEnd_692572 := by
    simpa [prefixWord, tailWord_692572, baseEnd_692572] using wordTrace_append hprefix tailTrace_692572
  have hstable : (prefixWord ++ tailWord_692572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692572).length < 2 ^ (prefixWord ++ tailWord_692572).sum := by decide
  have hdescent : baseEnd_692572 < baseStart_692572 := by decide
  rcases family_descends (prefixWord ++ tailWord_692572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692632 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_692632 : Nat := 118140960795 + 692632 * 2 ^ 59
def prefixEnd_692632 : Nat := 4983230072969 + 3 ^ 40 * 692632 * 2
def baseEnd_692632 : Nat := 237102088456692871876433

theorem tailTrace_692632 : CollatzResearch.WordTrace tailWord_692632 prefixEnd_692632 237102088456692871876433 := by
  unfold tailWord_692632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631182213360015486496075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16841576284480020648661433 12631182213360015486496075)
  ·
    refine ⟨18946773320040023229744113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12631182213360015486496075 18946773320040023229744113)
    ·
      refine ⟨14210079990030017422308085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18946773320040023229744113 14210079990030017422308085)
      ·
        refine ⟨1332194999065314133341383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14210079990030017422308085 1332194999065314133341383)
        ·
          refine ⟨1998292498597971200012075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332194999065314133341383 1998292498597971200012075)
          ·
            refine ⟨2997438747896956800018113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998292498597971200012075 2997438747896956800018113)
            ·
              refine ⟨2248079060922717600013585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997438747896956800018113 2248079060922717600013585)
              ·
                refine ⟨1686059295692038200010189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248079060922717600013585 1686059295692038200010189)
                ·
                  refine ⟨632272235884514325003821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1686059295692038200010189 632272235884514325003821)
                  ·
                    refine ⟨237102088456692871876433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632272235884514325003821 237102088456692871876433)
                    ·
                      rfl

theorem cell22_692632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_692632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692632 prefixEnd_692632 := by exact prefixLift 692632
  have htrace : WordTrace (prefixWord ++ tailWord_692632) baseStart_692632 baseEnd_692632 := by
    simpa [prefixWord, tailWord_692632, baseEnd_692632] using wordTrace_append hprefix tailTrace_692632
  have hstable : (prefixWord ++ tailWord_692632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692632).length < 2 ^ (prefixWord ++ tailWord_692632).sum := by decide
  have hdescent : baseEnd_692632 < baseStart_692632 := by decide
  rcases family_descends (prefixWord ++ tailWord_692632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692692 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_692692 : Nat := 118140960795 + 692692 * 2 ^ 59
def prefixEnd_692692 : Nat := 4983230072969 + 3 ^ 40 * 692692 * 2
def baseEnd_692692 : Nat := 237122627682872715376249

theorem tailTrace_692692 : CollatzResearch.WordTrace tailWord_692692 prefixEnd_692692 237122627682872715376249 := by
  unfold tailWord_692692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632276403251330610088165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16843035204335107480117553 12632276403251330610088165)
  ·
    refine ⟨2368551825609624489391531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12632276403251330610088165 2368551825609624489391531)
    ·
      refine ⟨3552827738414436734087297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368551825609624489391531 3552827738414436734087297)
      ·
        refine ⟨2664620803810827550565473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3552827738414436734087297 2664620803810827550565473)
        ·
          refine ⟨1998465602858120662924105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2664620803810827550565473 1998465602858120662924105)
          ·
            refine ⟨1498849202143590497193079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998465602858120662924105 1498849202143590497193079)
            ·
              refine ⟨2248273803215385745789619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498849202143590497193079 2248273803215385745789619)
              ·
                refine ⟨3372410704823078618684429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248273803215385745789619 3372410704823078618684429)
                ·
                  refine ⟨1264654014308654482006661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3372410704823078618684429 1264654014308654482006661)
                  ·
                    refine ⟨237122627682872715376249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264654014308654482006661 237122627682872715376249)
                    ·
                      rfl

theorem cell22_692692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_692692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692692 prefixEnd_692692 := by exact prefixLift 692692
  have htrace : WordTrace (prefixWord ++ tailWord_692692) baseStart_692692 baseEnd_692692 := by
    simpa [prefixWord, tailWord_692692, baseEnd_692692] using wordTrace_append hprefix tailTrace_692692
  have hstable : (prefixWord ++ tailWord_692692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692692).length < 2 ^ (prefixWord ++ tailWord_692692).sum := by decide
  have hdescent : baseEnd_692692 < baseStart_692692 := by decide
  rcases family_descends (prefixWord ++ tailWord_692692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692705 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_692705 : Nat := 118140960795 + 692705 * 2 ^ 59
def prefixEnd_692705 : Nat := 4983230072969 + 3 ^ 40 * 692705 * 2
def baseEnd_692705 : Nat := 237127077848545014801209

theorem tailTrace_692705 : CollatzResearch.WordTrace tailWord_692705 prefixEnd_692705 237127077848545014801209 := by
  unfold tailWord_692705
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265026955455564440399569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16843351303637042960266379 25265026955455564440399569)
  ·
    refine ⟨18948770216591673330299677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25265026955455564440399569 18948770216591673330299677)
    ·
      refine ⟨7105788831221877498862379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18948770216591673330299677 7105788831221877498862379)
      ·
        refine ⟨10658683246832816248293569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7105788831221877498862379 10658683246832816248293569)
        ·
          refine ⟨7994012435124612186220177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10658683246832816248293569 7994012435124612186220177)
          ·
            refine ⟨5995509326343459139665133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7994012435124612186220177 5995509326343459139665133)
            ·
              refine ⟨2248315997378797177374425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5995509326343459139665133 2248315997378797177374425)
              ·
                refine ⟨1686236998034097883030819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248315997378797177374425 1686236998034097883030819)
                ·
                  refine ⟨2529355497051146824546229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686236998034097883030819 2529355497051146824546229)
                  ·
                    refine ⟨237127077848545014801209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2529355497051146824546229 237127077848545014801209)
                    ·
                      rfl

theorem cell22_692705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_692705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692705 prefixEnd_692705 := by exact prefixLift 692705
  have htrace : WordTrace (prefixWord ++ tailWord_692705) baseStart_692705 baseEnd_692705 := by
    simpa [prefixWord, tailWord_692705, baseEnd_692705] using wordTrace_append hprefix tailTrace_692705
  have hstable : (prefixWord ++ tailWord_692705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692705).length < 2 ^ (prefixWord ++ tailWord_692705).sum := by decide
  have hdescent : baseEnd_692705 < baseStart_692705 := by decide
  rcases family_descends (prefixWord ++ tailWord_692705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692720 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_692720 : Nat := 118140960795 + 692720 * 2 ^ 59
def prefixEnd_692720 : Nat := 4983230072969 + 3 ^ 40 * 692720 * 2
def baseEnd_692720 : Nat := 237132212655089975676163

theorem tailTrace_692720 : CollatzResearch.WordTrace tailWord_692720 prefixEnd_692720 237132212655089975676163 := by
  unfold tailWord_692720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632787025200611001097807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16843716033600814668130409 12632787025200611001097807)
  ·
    refine ⟨18949180537800916501646711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12632787025200611001097807 18949180537800916501646711)
    ·
      refine ⟨28423770806701374752470067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18949180537800916501646711 28423770806701374752470067)
      ·
        refine ⟨42635656210052062128705101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28423770806701374752470067 42635656210052062128705101)
        ·
          refine ⟨15988371078769523298264413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42635656210052062128705101 15988371078769523298264413)
          ·
            refine ⟨5995639154538571236849155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15988371078769523298264413 5995639154538571236849155)
            ·
              refine ⟨8993458731807856855273733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995639154538571236849155 8993458731807856855273733)
              ·
                refine ⟨1686273512213973160363825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8993458731807856855273733 1686273512213973160363825)
                ·
                  refine ⟨1264705134160479870272869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686273512213973160363825 1264705134160479870272869)
                  ·
                    refine ⟨237132212655089975676163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264705134160479870272869 237132212655089975676163)
                    ·
                      rfl

theorem cell22_692720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_692720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692720 prefixEnd_692720 := by exact prefixLift 692720
  have htrace : WordTrace (prefixWord ++ tailWord_692720) baseStart_692720 baseEnd_692720 := by
    simpa [prefixWord, tailWord_692720, baseEnd_692720] using wordTrace_append hprefix tailTrace_692720
  have hstable : (prefixWord ++ tailWord_692720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692720).length < 2 ^ (prefixWord ++ tailWord_692720).sum := by decide
  have hdescent : baseEnd_692720 < baseStart_692720 := by decide
  rcases family_descends (prefixWord ++ tailWord_692720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692784 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 1, 3]
def baseStart_692784 : Nat := 118140960795 + 692784 * 2 ^ 59
def prefixEnd_692784 : Nat := 4983230072969 + 3 ^ 40 * 692784 * 2
def baseEnd_692784 : Nat := 237154121163015142075967

theorem tailTrace_692784 : CollatzResearch.WordTrace tailWord_692784 prefixEnd_692784 237154121163015142075967 := by
  unfold tailWord_692784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633954161084680466262703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16845272214779573955016937 12633954161084680466262703)
  ·
    refine ⟨18950931241627020699394055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12633954161084680466262703 18950931241627020699394055)
    ·
      refine ⟨28426396862440531049091083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18950931241627020699394055 28426396862440531049091083)
      ·
        refine ⟨42639595293660796573636625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28426396862440531049091083 42639595293660796573636625)
        ·
          refine ⟨31979696470245597430227469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42639595293660796573636625 31979696470245597430227469)
          ·
            refine ⟨11992386176342099036335301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31979696470245597430227469 11992386176342099036335301)
            ·
              refine ⟨2248572408064143569312869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11992386176342099036335301 2248572408064143569312869)
              ·
                refine ⟨421607326512026919246163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2248572408064143569312869 421607326512026919246163)
                ·
                  refine ⟨632410989768040378869245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421607326512026919246163 632410989768040378869245)
                  ·
                    refine ⟨237154121163015142075967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632410989768040378869245 237154121163015142075967)
                    ·
                      rfl

theorem cell22_692784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_692784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692784 prefixEnd_692784 := by exact prefixLift 692784
  have htrace : WordTrace (prefixWord ++ tailWord_692784) baseStart_692784 baseEnd_692784 := by
    simpa [prefixWord, tailWord_692784, baseEnd_692784] using wordTrace_append hprefix tailTrace_692784
  have hstable : (prefixWord ++ tailWord_692784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692784).length < 2 ^ (prefixWord ++ tailWord_692784).sum := by decide
  have hdescent : baseEnd_692784 < baseStart_692784 := by decide
  rcases family_descends (prefixWord ++ tailWord_692784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692855 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_692855 : Nat := 118140960795 + 692855 * 2 ^ 59
def prefixEnd_692855 : Nat := 4983230072969 + 3 ^ 40 * 692855 * 2
def baseEnd_692855 : Nat := 237178425913994623550749

theorem tailTrace_692855 : CollatzResearch.WordTrace tailWord_692855 prefixEnd_692855 237178425913994623550749 := by
  unfold tailWord_692855
  simp only [CollatzResearch.WordTrace]
  refine ⟨25270497904912140058360019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16846998603274760038906679 25270497904912140058360019)
  ·
    refine ⟨37905746857368210087540029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25270497904912140058360019 37905746857368210087540029)
    ·
      refine ⟨14214655071513078782827511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37905746857368210087540029 14214655071513078782827511)
      ·
        refine ⟨21321982607269618174241267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14214655071513078782827511 21321982607269618174241267)
        ·
          refine ⟨31982973910904427261361901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21321982607269618174241267 31982973910904427261361901)
          ·
            refine ⟨11993615216589160223010713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31982973910904427261361901 11993615216589160223010713)
            ·
              refine ⟨8995211412441870167258035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11993615216589160223010713 8995211412441870167258035)
              ·
                refine ⟨13492817118662805250887053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8995211412441870167258035 13492817118662805250887053)
                ·
                  refine ⟨5059806419498551969082645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13492817118662805250887053 5059806419498551969082645)
                  ·
                    refine ⟨237178425913994623550749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5059806419498551969082645 237178425913994623550749)
                    ·
                      rfl

theorem cell22_692855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_692855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692855 prefixEnd_692855 := by exact prefixLift 692855
  have htrace : WordTrace (prefixWord ++ tailWord_692855) baseStart_692855 baseEnd_692855 := by
    simpa [prefixWord, tailWord_692855, baseEnd_692855] using wordTrace_append hprefix tailTrace_692855
  have hstable : (prefixWord ++ tailWord_692855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692855).length < 2 ^ (prefixWord ++ tailWord_692855).sum := by decide
  have hdescent : baseEnd_692855 < baseStart_692855 := by decide
  rcases family_descends (prefixWord ++ tailWord_692855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692861 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_692861 : Nat := 118140960795 + 692861 * 2 ^ 59
def prefixEnd_692861 : Nat := 4983230072969 + 3 ^ 40 * 692861 * 2
def baseEnd_692861 : Nat := 237180479836612607900731

theorem tailTrace_692861 : CollatzResearch.WordTrace tailWord_692861 prefixEnd_692861 237180479836612607900731 := by
  unfold tailWord_692861
  simp only [CollatzResearch.WordTrace]
  refine ⟨25270716742890403083078437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16847144495260268722052291 25270716742890403083078437)
  ·
    refine ⟨4738259389291950578077207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25270716742890403083078437 4738259389291950578077207)
    ·
      refine ⟨7107389083937925867115811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4738259389291950578077207 7107389083937925867115811)
      ·
        refine ⟨10661083625906888800673717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7107389083937925867115811 10661083625906888800673717)
        ·
          refine ⟨999476589928770825063161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10661083625906888800673717 999476589928770825063161)
          ·
            refine ⟨749607442446578118797371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999476589928770825063161 749607442446578118797371)
            ·
              refine ⟨1124411163669867178196057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749607442446578118797371 1124411163669867178196057)
              ·
                refine ⟨843308372752400383647043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124411163669867178196057 843308372752400383647043)
                ·
                  refine ⟨1264962559128600575470565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843308372752400383647043 1264962559128600575470565)
                  ·
                    refine ⟨237180479836612607900731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264962559128600575470565 237180479836612607900731)
                    ·
                      rfl

theorem cell22_692861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_692861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692861 prefixEnd_692861 := by exact prefixLift 692861
  have htrace : WordTrace (prefixWord ++ tailWord_692861) baseStart_692861 baseEnd_692861 := by
    simpa [prefixWord, tailWord_692861, baseEnd_692861] using wordTrace_append hprefix tailTrace_692861
  have hstable : (prefixWord ++ tailWord_692861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692861).length < 2 ^ (prefixWord ++ tailWord_692861).sum := by decide
  have hdescent : baseEnd_692861 < baseStart_692861 := by decide
  rcases family_descends (prefixWord ++ tailWord_692861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692874 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_692874 : Nat := 118140960795 + 692874 * 2 ^ 59
def prefixEnd_692874 : Nat := 4983230072969 + 3 ^ 40 * 692874 * 2
def baseEnd_692874 : Nat := 237184930002284907325691

theorem tailTrace_692874 : CollatzResearch.WordTrace tailWord_692874 prefixEnd_692874 237184930002284907325691 := by
  unfold tailWord_692874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317797722960826575825419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16847460594562204202201117 6317797722960826575825419)
  ·
    refine ⟨9476696584441239863738129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317797722960826575825419 9476696584441239863738129)
    ·
      refine ⟨7107522438330929897803597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9476696584441239863738129 7107522438330929897803597)
      ·
        refine ⟨2665320914374098711676349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7107522438330929897803597 2665320914374098711676349)
        ·
          refine ⟨999495342890287016878631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2665320914374098711676349 999495342890287016878631)
          ·
            refine ⟨1499243014335430525317947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999495342890287016878631 1499243014335430525317947)
            ·
              refine ⟨2248864521503145787976921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499243014335430525317947 2248864521503145787976921)
              ·
                refine ⟨1686648391127359340982691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248864521503145787976921 1686648391127359340982691)
                ·
                  refine ⟨2529972586691039011474037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686648391127359340982691 2529972586691039011474037)
                  ·
                    refine ⟨237184930002284907325691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2529972586691039011474037 237184930002284907325691)
                    ·
                      rfl

theorem cell22_692874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_692874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692874 prefixEnd_692874 := by exact prefixLift 692874
  have htrace : WordTrace (prefixWord ++ tailWord_692874) baseStart_692874 baseEnd_692874 := by
    simpa [prefixWord, tailWord_692874, baseEnd_692874] using wordTrace_append hprefix tailTrace_692874
  have hstable : (prefixWord ++ tailWord_692874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692874).length < 2 ^ (prefixWord ++ tailWord_692874).sum := by decide
  have hdescent : baseEnd_692874 < baseStart_692874 := by decide
  rcases family_descends (prefixWord ++ tailWord_692874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692936 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 1, 3]
def baseStart_692936 : Nat := 118140960795 + 692936 * 2 ^ 59
def prefixEnd_692936 : Nat := 4983230072969 + 3 ^ 40 * 692936 * 2
def baseEnd_692936 : Nat := 237206153869337412275501

theorem tailTrace_692936 : CollatzResearch.WordTrace tailWord_692936 prefixEnd_692936 237206153869337412275501 := by
  unfold tailWord_692936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12636726108809345446029331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16848968145079127261372441 12636726108809345446029331)
  ·
    refine ⟨18955089163214018169043997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12636726108809345446029331 18955089163214018169043997)
    ·
      refine ⟨7108158436205256813391499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18955089163214018169043997 7108158436205256813391499)
      ·
        refine ⟨10662237654307885220087249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108158436205256813391499 10662237654307885220087249)
        ·
          refine ⟨7996678240730913915065437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10662237654307885220087249 7996678240730913915065437)
          ·
            refine ⟨2998754340274092718149539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7996678240730913915065437 2998754340274092718149539)
            ·
              refine ⟨4498131510411139077224309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998754340274092718149539 4498131510411139077224309)
              ·
                refine ⟨421699829101044288489779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4498131510411139077224309 421699829101044288489779)
                ·
                  refine ⟨632549743651566432734669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421699829101044288489779 632549743651566432734669)
                  ·
                    refine ⟨237206153869337412275501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632549743651566432734669 237206153869337412275501)
                    ·
                      rfl

theorem cell22_692936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_692936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692936 prefixEnd_692936 := by exact prefixLift 692936
  have htrace : WordTrace (prefixWord ++ tailWord_692936) baseStart_692936 baseEnd_692936 := by
    simpa [prefixWord, tailWord_692936, baseEnd_692936] using wordTrace_append hprefix tailTrace_692936
  have hstable : (prefixWord ++ tailWord_692936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692936).length < 2 ^ (prefixWord ++ tailWord_692936).sum := by decide
  have hdescent : baseEnd_692936 < baseStart_692936 := by decide
  rcases family_descends (prefixWord ++ tailWord_692936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692977 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 6]
def baseStart_692977 : Nat := 118140960795 + 692977 * 2 ^ 59
def prefixEnd_692977 : Nat := 4983230072969 + 3 ^ 40 * 692977 * 2
def baseEnd_692977 : Nat := 79073396335742324000125

theorem tailTrace_692977 : CollatzResearch.WordTrace tailWord_692977 prefixEnd_692977 79073396335742324000125 := by
  unfold tailWord_692977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25274947610470154894301185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16849965073646769929534123 25274947610470154894301185)
  ·
    refine ⟨18956210707852616170725889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25274947610470154894301185 18956210707852616170725889)
    ·
      refine ⟨14217158030889462128044417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18956210707852616170725889 14217158030889462128044417)
      ·
        refine ⟨10662868523167096596033313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14217158030889462128044417 10662868523167096596033313)
        ·
          refine ⟨7997151392375322447024985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10662868523167096596033313 7997151392375322447024985)
          ·
            refine ⟨5997863544281491835268739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997151392375322447024985 5997863544281491835268739)
            ·
              refine ⟨8996795316422237752903109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997863544281491835268739 8996795316422237752903109)
              ·
                refine ⟨1686899121829169578669333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8996795316422237752903109 1686899121829169578669333)
                ·
                  refine ⟨79073396335742324000125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1686899121829169578669333 79073396335742324000125)
                  ·
                    rfl

theorem cell22_692977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_692977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_692977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_692977 prefixEnd_692977 := by exact prefixLift 692977
  have htrace : WordTrace (prefixWord ++ tailWord_692977) baseStart_692977 baseEnd_692977 := by
    simpa [prefixWord, tailWord_692977, baseEnd_692977] using wordTrace_append hprefix tailTrace_692977
  have hstable : (prefixWord ++ tailWord_692977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692977).length < 2 ^ (prefixWord ++ tailWord_692977).sum := by decide
  have hdescent : baseEnd_692977 < baseStart_692977 := by decide
  rcases family_descends (prefixWord ++ tailWord_692977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693009 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_693009 : Nat := 118140960795 + 693009 * 2 ^ 59
def prefixEnd_693009 : Nat := 4983230072969 + 3 ^ 40 * 693009 * 2
def baseEnd_693009 : Nat := 237231143261189555200277

theorem tailTrace_693009 : CollatzResearch.WordTrace tailWord_693009 prefixEnd_693009 237231143261189555200277 := by
  unfold tailWord_693009
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276114746354224359466081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16850743164236149572977387 25276114746354224359466081)
  ·
    refine ⟨18957086059765668269599561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25276114746354224359466081 18957086059765668269599561)
    ·
      refine ⟨14217814544824251202199671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18957086059765668269599561 14217814544824251202199671)
      ·
        refine ⟨21326721817236376803299507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217814544824251202199671 21326721817236376803299507)
        ·
          refine ⟨31990082725854565204949261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21326721817236376803299507 31990082725854565204949261)
          ·
            refine ⟨11996281022195461951855973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31990082725854565204949261 11996281022195461951855973)
            ·
              refine ⟨2249302691661649115972995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11996281022195461951855973 2249302691661649115972995)
              ·
                refine ⟨3373954037492473673959493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249302691661649115972995 3373954037492473673959493)
                ·
                  refine ⟨632616382029838813867405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3373954037492473673959493 632616382029838813867405)
                  ·
                    refine ⟨237231143261189555200277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632616382029838813867405 237231143261189555200277)
                    ·
                      rfl

theorem cell22_693009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_693009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693009 prefixEnd_693009 := by exact prefixLift 693009
  have htrace : WordTrace (prefixWord ++ tailWord_693009) baseStart_693009 baseEnd_693009 := by
    simpa [prefixWord, tailWord_693009, baseEnd_693009] using wordTrace_append hprefix tailTrace_693009
  have hstable : (prefixWord ++ tailWord_693009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693009).length < 2 ^ (prefixWord ++ tailWord_693009).sum := by decide
  have hdescent : baseEnd_693009 < baseStart_693009 := by decide
  rcases family_descends (prefixWord ++ tailWord_693009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693011 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 4]
def baseStart_693011 : Nat := 118140960795 + 693011 * 2 ^ 59
def prefixEnd_693011 : Nat := 4983230072969 + 3 ^ 40 * 693011 * 2
def baseEnd_693011 : Nat := 79077275967354072216757

theorem tailTrace_693011 : CollatzResearch.WordTrace tailWord_693011 prefixEnd_693011 79077275967354072216757 := by
  unfold tailWord_693011
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276187692346978701038887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16850791794897985800692591 25276187692346978701038887)
  ·
    refine ⟨37914281538520468051558331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25276187692346978701038887 37914281538520468051558331)
    ·
      refine ⟨56871422307780702077337497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37914281538520468051558331 56871422307780702077337497)
      ·
        refine ⟨42653566730835526558003123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56871422307780702077337497 42653566730835526558003123)
        ·
          refine ⟨63980350096253289837004685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42653566730835526558003123 63980350096253289837004685)
          ·
            refine ⟨23992631286094983688876757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63980350096253289837004685 23992631286094983688876757)
            ·
              refine ⟨562327295767851180208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23992631286094983688876757 562327295767851180208049)
              ·
                refine ⟨421745471825888385156037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562327295767851180208049 421745471825888385156037)
                ·
                  refine ⟨79077275967354072216757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421745471825888385156037 79077275967354072216757)
                  ·
                    rfl

theorem cell22_693011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 4].length) (baseStart_693011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693011 prefixEnd_693011 := by exact prefixLift 693011
  have htrace : WordTrace (prefixWord ++ tailWord_693011) baseStart_693011 baseEnd_693011 := by
    simpa [prefixWord, tailWord_693011, baseEnd_693011] using wordTrace_append hprefix tailTrace_693011
  have hstable : (prefixWord ++ tailWord_693011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693011).length < 2 ^ (prefixWord ++ tailWord_693011).sum := by decide
  have hdescent : baseEnd_693011 < baseStart_693011 := by decide
  rcases family_descends (prefixWord ++ tailWord_693011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693118 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_693118 : Nat := 118140960795 + 693118 * 2 ^ 59
def prefixEnd_693118 : Nat := 4983230072969 + 3 ^ 40 * 693118 * 2
def baseEnd_693118 : Nat := 79089485396249868074981

theorem tailTrace_693118 : CollatzResearch.WordTrace tailWord_693118 prefixEnd_693118 79089485396249868074981 := by
  unfold tailWord_693118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160011287869916996898001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16853393535306223983456005 3160011287869916996898001)
  ·
    refine ⟨2370008465902437747673501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160011287869916996898001 2370008465902437747673501)
    ·
      refine ⟨888753174713414155377563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2370008465902437747673501 888753174713414155377563)
      ·
        refine ⟨1333129762070121233066345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888753174713414155377563 1333129762070121233066345)
        ·
          refine ⟨999847321552590924799759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333129762070121233066345 999847321552590924799759)
          ·
            refine ⟨1499770982328886387199639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999847321552590924799759 1499770982328886387199639)
            ·
              refine ⟨2249656473493329580799459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499770982328886387199639 2249656473493329580799459)
              ·
                refine ⟨3374484710239994371199189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249656473493329580799459 3374484710239994371199189)
                ·
                  refine ⟨79089485396249868074981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3374484710239994371199189 79089485396249868074981)
                  ·
                    rfl

theorem cell22_693118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_693118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693118 prefixEnd_693118 := by exact prefixLift 693118
  have htrace : WordTrace (prefixWord ++ tailWord_693118) baseStart_693118 baseEnd_693118 := by
    simpa [prefixWord, tailWord_693118, baseEnd_693118] using wordTrace_append hprefix tailTrace_693118
  have hstable : (prefixWord ++ tailWord_693118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693118).length < 2 ^ (prefixWord ++ tailWord_693118).sum := by decide
  have hdescent : baseEnd_693118 < baseStart_693118 := by decide
  rcases family_descends (prefixWord ++ tailWord_693118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693122 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_693122 : Nat := 118140960795 + 693122 * 2 ^ 59
def prefixEnd_693122 : Nat := 4983230072969 + 3 ^ 40 * 693122 * 2
def baseEnd_693122 : Nat := 237269825470494927124931

theorem tailTrace_693122 : CollatzResearch.WordTrace tailWord_693122 prefixEnd_693122 237269825470494927124931 := by
  unfold tailWord_693122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320059048736211164582405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16853490796629896438886413 6320059048736211164582405)
  ·
    refine ⟨1185011071638039593359201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6320059048736211164582405 1185011071638039593359201)
    ·
      refine ⟨888758303728529695019401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185011071638039593359201 888758303728529695019401)
      ·
        refine ⟨666568727796397271264551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888758303728529695019401 666568727796397271264551)
        ·
          refine ⟨999853091694595906896827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666568727796397271264551 999853091694595906896827)
          ·
            refine ⟨1499779637541893860345241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999853091694595906896827 1499779637541893860345241)
            ·
              refine ⟨1124834728156420395258931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499779637541893860345241 1124834728156420395258931)
              ·
                refine ⟨1687252092234630592888397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124834728156420395258931 1687252092234630592888397)
                ·
                  refine ⟨632719534587986472333149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1687252092234630592888397 632719534587986472333149)
                  ·
                    refine ⟨237269825470494927124931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632719534587986472333149 237269825470494927124931)
                    ·
                      rfl

theorem cell22_693122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_693122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693122 prefixEnd_693122 := by exact prefixLift 693122
  have htrace : WordTrace (prefixWord ++ tailWord_693122) baseStart_693122 baseEnd_693122 := by
    simpa [prefixWord, tailWord_693122, baseEnd_693122] using wordTrace_append hprefix tailTrace_693122
  have hstable : (prefixWord ++ tailWord_693122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693122).length < 2 ^ (prefixWord ++ tailWord_693122).sum := by decide
  have hdescent : baseEnd_693122 < baseStart_693122 := by decide
  rcases family_descends (prefixWord ++ tailWord_693122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693129 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 6]
def baseStart_693129 : Nat := 118140960795 + 693129 * 2 ^ 59
def prefixEnd_693129 : Nat := 4983230072969 + 3 ^ 40 * 693129 * 2
def baseEnd_693129 : Nat := 79090740571183080733303

theorem tailTrace_693129 : CollatzResearch.WordTrace tailWord_693129 prefixEnd_693129 79090740571183080733303 := by
  unfold tailWord_693129
  simp only [CollatzResearch.WordTrace]
  refine ⟨25280491505919484853834441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16853661003946323235889627 25280491505919484853834441)
  ·
    refine ⟨18960368629439613640375831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25280491505919484853834441 18960368629439613640375831)
    ·
      refine ⟨28440552944159420460563747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18960368629439613640375831 28440552944159420460563747)
      ·
        refine ⟨42660829416239130690845621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28440552944159420460563747 42660829416239130690845621)
        ·
          refine ⟨3999452757772418502266777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42660829416239130690845621 3999452757772418502266777)
          ·
            refine ⟨2999589568329313876700083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999452757772418502266777 2999589568329313876700083)
            ·
              refine ⟨4499384352493970815050125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999589568329313876700083 4499384352493970815050125)
              ·
                refine ⟨1687269132185239055643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4499384352493970815050125 1687269132185239055643797)
                ·
                  refine ⟨79090740571183080733303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1687269132185239055643797 79090740571183080733303)
                  ·
                    rfl

theorem cell22_693129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_693129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693129 prefixEnd_693129 := by exact prefixLift 693129
  have htrace : WordTrace (prefixWord ++ tailWord_693129) baseStart_693129 baseEnd_693129 := by
    simpa [prefixWord, tailWord_693129, baseEnd_693129] using wordTrace_append hprefix tailTrace_693129
  have hstable : (prefixWord ++ tailWord_693129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693129).length < 2 ^ (prefixWord ++ tailWord_693129).sum := by decide
  have hdescent : baseEnd_693129 < baseStart_693129 := by decide
  rcases family_descends (prefixWord ++ tailWord_693129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693176 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_693176 : Nat := 118140960795 + 693176 * 2 ^ 59
def prefixEnd_693176 : Nat := 4983230072969 + 3 ^ 40 * 693176 * 2
def baseEnd_693176 : Nat := 237288310774056786274765

theorem tailTrace_693176 : CollatzResearch.WordTrace tailWord_693176 prefixEnd_693176 237288310774056786274765 := by
  unfold tailWord_693176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641102868374605940397691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16854803824499474587196921 12641102868374605940397691)
  ·
    refine ⟨18961654302561908910596537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641102868374605940397691 18961654302561908910596537)
    ·
      refine ⟨14221240726921431682947403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18961654302561908910596537 14221240726921431682947403)
      ·
        refine ⟨21331861090382147524421105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14221240726921431682947403 21331861090382147524421105)
        ·
          refine ⟨15998895817786610643315829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21331861090382147524421105 15998895817786610643315829)
          ·
            refine ⟨1499896482917494747810859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15998895817786610643315829 1499896482917494747810859)
            ·
              refine ⟨2249844724376242121716289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499896482917494747810859 2249844724376242121716289)
              ·
                refine ⟨1687383543282181591287217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249844724376242121716289 1687383543282181591287217)
                ·
                  refine ⟨1265537657461636193465413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687383543282181591287217 1265537657461636193465413)
                  ·
                    refine ⟨237288310774056786274765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265537657461636193465413 237288310774056786274765)
                    ·
                      rfl

theorem cell22_693176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_693176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693176 prefixEnd_693176 := by exact prefixLift 693176
  have htrace : WordTrace (prefixWord ++ tailWord_693176) baseStart_693176 baseEnd_693176 := by
    simpa [prefixWord, tailWord_693176, baseEnd_693176] using wordTrace_append hprefix tailTrace_693176
  have hstable : (prefixWord ++ tailWord_693176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693176).length < 2 ^ (prefixWord ++ tailWord_693176).sum := by decide
  have hdescent : baseEnd_693176 < baseStart_693176 := by decide
  rcases family_descends (prefixWord ++ tailWord_693176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693195 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 2, 3]
def baseStart_693195 : Nat := 118140960795 + 693195 * 2 ^ 59
def prefixEnd_693195 : Nat := 4983230072969 + 3 ^ 40 * 693195 * 2
def baseEnd_693195 : Nat := 237294814862347070049707

theorem tailTrace_693195 : CollatzResearch.WordTrace tailWord_693195 prefixEnd_693195 237294814862347070049707 := by
  unfold tailWord_693195
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282898723680378125737039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16855265815786918750491359 25282898723680378125737039)
  ·
    refine ⟨37924348085520567188605559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25282898723680378125737039 37924348085520567188605559)
    ·
      refine ⟨56886522128280850782908339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37924348085520567188605559 56886522128280850782908339)
      ·
        refine ⟨85329783192421276174362509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56886522128280850782908339 85329783192421276174362509)
        ·
          refine ⟨31998668697157978565385941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85329783192421276174362509 31998668697157978565385941)
          ·
            refine ⟨749968797589640122626233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31998668697157978565385941 749968797589640122626233)
            ·
              refine ⟨562476598192230091969675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749968797589640122626233 562476598192230091969675)
              ·
                refine ⟨843714897288345137954513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562476598192230091969675 843714897288345137954513)
                ·
                  refine ⟨632786172966258853465885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843714897288345137954513 632786172966258853465885)
                  ·
                    refine ⟨237294814862347070049707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632786172966258853465885 237294814862347070049707)
                    ·
                      rfl

theorem cell22_693195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 3].length) (baseStart_693195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693195 prefixEnd_693195 := by exact prefixLift 693195
  have htrace : WordTrace (prefixWord ++ tailWord_693195) baseStart_693195 baseEnd_693195 := by
    simpa [prefixWord, tailWord_693195, baseEnd_693195] using wordTrace_append hprefix tailTrace_693195
  have hstable : (prefixWord ++ tailWord_693195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693195).length < 2 ^ (prefixWord ++ tailWord_693195).sum := by decide
  have hdescent : baseEnd_693195 < baseStart_693195 := by decide
  rcases family_descends (prefixWord ++ tailWord_693195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693283 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 1, 4]
def baseStart_693283 : Nat := 118140960795 + 693283 * 2 ^ 59
def prefixEnd_693283 : Nat := 4983230072969 + 3 ^ 40 * 693283 * 2
def baseEnd_693283 : Nat := 237324939060744173849437

theorem tailTrace_693283 : CollatzResearch.WordTrace tailWord_693283 prefixEnd_693283 237324939060744173849437 := by
  unfold tailWord_693283
  simp only [CollatzResearch.WordTrace]
  refine ⟨25286108347361569154940503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16857405564907712769960335 25286108347361569154940503)
  ·
    refine ⟨37929162521042353732410755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25286108347361569154940503 37929162521042353732410755)
    ·
      refine ⟨56893743781563530598616133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37929162521042353732410755 56893743781563530598616133)
      ·
        refine ⟨10667576959043161987240525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56893743781563530598616133 10667576959043161987240525)
        ·
          refine ⟨4000341359641185745215197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10667576959043161987240525 4000341359641185745215197)
          ·
            refine ⟨1500128009865444654455699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4000341359641185745215197 1500128009865444654455699)
            ·
              refine ⟨2250192014798166981683549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500128009865444654455699 2250192014798166981683549)
              ·
                refine ⟨843822005549312618131331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2250192014798166981683549 843822005549312618131331)
                ·
                  refine ⟨1265733008323968927196997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843822005549312618131331 1265733008323968927196997)
                  ·
                    refine ⟨237324939060744173849437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265733008323968927196997 237324939060744173849437)
                    ·
                      rfl

theorem cell22_693283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 4].length) (baseStart_693283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693283 prefixEnd_693283 := by exact prefixLift 693283
  have htrace : WordTrace (prefixWord ++ tailWord_693283) baseStart_693283 baseEnd_693283 := by
    simpa [prefixWord, tailWord_693283, baseEnd_693283] using wordTrace_append hprefix tailTrace_693283
  have hstable : (prefixWord ++ tailWord_693283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693283).length < 2 ^ (prefixWord ++ tailWord_693283).sum := by decide
  have hdescent : baseEnd_693283 < baseStart_693283 := by decide
  rcases family_descends (prefixWord ++ tailWord_693283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693298 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_693298 : Nat := 118140960795 + 693298 * 2 ^ 59
def prefixEnd_693298 : Nat := 4983230072969 + 3 ^ 40 * 693298 * 2
def baseEnd_693298 : Nat := 79110024622429711574797

theorem tailTrace_693298 : CollatzResearch.WordTrace tailWord_693298 prefixEnd_693298 79110024622429711574797 := by
  unfold tailWord_693298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321663860576806679184137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16857770294871484477824365 6321663860576806679184137)
  ·
    refine ⟨4741247895432605009388103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6321663860576806679184137 4741247895432605009388103)
    ·
      refine ⟨7111871843148907514082155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741247895432605009388103 7111871843148907514082155)
      ·
        refine ⟨10667807764723361271123233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7111871843148907514082155 10667807764723361271123233)
        ·
          refine ⟨8000855823542520953342425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10667807764723361271123233 8000855823542520953342425)
          ·
            refine ⟨6000641867656890715006819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8000855823542520953342425 6000641867656890715006819)
            ·
              refine ⟨9000962801485336072510229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000641867656890715006819 9000962801485336072510229)
              ·
                refine ⟨421920131319625128398917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9000962801485336072510229 421920131319625128398917)
                ·
                  refine ⟨79110024622429711574797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421920131319625128398917 79110024622429711574797)
                  ·
                    rfl

theorem cell22_693298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_693298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693298 prefixEnd_693298 := by exact prefixLift 693298
  have htrace : WordTrace (prefixWord ++ tailWord_693298) baseStart_693298 baseEnd_693298 := by
    simpa [prefixWord, tailWord_693298, baseEnd_693298] using wordTrace_append hprefix tailTrace_693298
  have hstable : (prefixWord ++ tailWord_693298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693298).length < 2 ^ (prefixWord ++ tailWord_693298).sum := by decide
  have hdescent : baseEnd_693298 < baseStart_693298 := by decide
  rcases family_descends (prefixWord ++ tailWord_693298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693326 : List Nat := [4, 1, 1, 1, 1, 3, 3, 8]
def baseStart_693326 : Nat := 118140960795 + 693326 * 2 ^ 59
def prefixEnd_693326 : Nat := 4983230072969 + 3 ^ 40 * 693326 * 2
def baseEnd_693326 : Nat := 26371073204389599447145

theorem tailTrace_693326 : CollatzResearch.WordTrace tailWord_693326 prefixEnd_693326 26371073204389599447145 := by
  unfold tailWord_693326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160959585775723437344479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16858451124137191665837221 3160959585775723437344479)
  ·
    refine ⟨4741439378663585156016719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3160959585775723437344479 4741439378663585156016719)
    ·
      refine ⟨7112159067995377734025079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741439378663585156016719 7112159067995377734025079)
      ·
        refine ⟨10668238601993066601037619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7112159067995377734025079 10668238601993066601037619)
        ·
          refine ⟨16002357902989599901556429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10668238601993066601037619 16002357902989599901556429)
          ·
            refine ⟨6000884213621099963083661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16002357902989599901556429 6000884213621099963083661)
            ·
              refine ⟨2250331580107912486156373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6000884213621099963083661 2250331580107912486156373)
              ·
                refine ⟨26371073204389599447145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2250331580107912486156373 26371073204389599447145)
                ·
                  rfl

theorem cell22_693326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_693326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693326 prefixEnd_693326 := by exact prefixLift 693326
  have htrace : WordTrace (prefixWord ++ tailWord_693326) baseStart_693326 baseEnd_693326 := by
    simpa [prefixWord, tailWord_693326, baseEnd_693326] using wordTrace_append hprefix tailTrace_693326
  have hstable : (prefixWord ++ tailWord_693326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693326).length < 2 ^ (prefixWord ++ tailWord_693326).sum := by decide
  have hdescent : baseEnd_693326 < baseStart_693326 := by decide
  rcases family_descends (prefixWord ++ tailWord_693326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693356 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_693356 : Nat := 118140960795 + 693356 * 2 ^ 59
def prefixEnd_693356 : Nat := 4983230072969 + 3 ^ 40 * 693356 * 2
def baseEnd_693356 : Nat := 237349928452596316774213

theorem tailTrace_693356 : CollatzResearch.WordTrace tailWord_693356 prefixEnd_693356 237349928452596316774213 := by
  unfold tailWord_693356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12644385438048551311173961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16859180584064735081565281 12644385438048551311173961)
  ·
    refine ⟨9483289078536413483380471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12644385438048551311173961 9483289078536413483380471)
    ·
      refine ⟨14224933617804620225070707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9483289078536413483380471 14224933617804620225070707)
      ·
        refine ⟨21337400426706930337606061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14224933617804620225070707 21337400426706930337606061)
        ·
          refine ⟨8001525160015098876602273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21337400426706930337606061 8001525160015098876602273)
          ·
            refine ⟨6001143870011324157451705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8001525160015098876602273 6001143870011324157451705)
            ·
              refine ⟨4500857902508493118088779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001143870011324157451705 4500857902508493118088779)
              ·
                refine ⟨6751286853762739677133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500857902508493118088779 6751286853762739677133169)
                ·
                  refine ⟨5063465140322054757849877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6751286853762739677133169 5063465140322054757849877)
                  ·
                    refine ⟨237349928452596316774213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5063465140322054757849877 237349928452596316774213)
                    ·
                      rfl

theorem cell22_693356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_693356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693356 prefixEnd_693356 := by exact prefixLift 693356
  have htrace : WordTrace (prefixWord ++ tailWord_693356) baseStart_693356 baseEnd_693356 := by
    simpa [prefixWord, tailWord_693356, baseEnd_693356] using wordTrace_append hprefix tailTrace_693356
  have hstable : (prefixWord ++ tailWord_693356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693356).length < 2 ^ (prefixWord ++ tailWord_693356).sum := by decide
  have hdescent : baseEnd_693356 < baseStart_693356 := by decide
  rcases family_descends (prefixWord ++ tailWord_693356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693433 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 6]
def baseStart_693433 : Nat := 118140960795 + 693433 * 2 ^ 59
def prefixEnd_693433 : Nat := 4983230072969 + 3 ^ 40 * 693433 * 2
def baseEnd_693433 : Nat := 79125429042064594199659

theorem tailTrace_693433 : CollatzResearch.WordTrace tailWord_693433 prefixEnd_693433 79125429042064594199659 := by
  unfold tailWord_693433
  simp only [CollatzResearch.WordTrace]
  refine ⟨25291579296818144772900953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16861052864545429848600635 25291579296818144772900953)
  ·
    refine ⟨18968684472613608579675715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25291579296818144772900953 18968684472613608579675715)
    ·
      refine ⟨28453026708920412869513573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18968684472613608579675715 28453026708920412869513573)
      ·
        refine ⟨5334942507922577413033795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28453026708920412869513573 5334942507922577413033795)
        ·
          refine ⟨8002413761883866119550693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334942507922577413033795 8002413761883866119550693)
          ·
            refine ⟨1500452580353224897415755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8002413761883866119550693 1500452580353224897415755)
            ·
              refine ⟨2250678870529837346123633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500452580353224897415755 2250678870529837346123633)
              ·
                refine ⟨1688009152897378009592725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250678870529837346123633 1688009152897378009592725)
                ·
                  refine ⟨79125429042064594199659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1688009152897378009592725 79125429042064594199659)
                  ·
                    rfl

theorem cell22_693433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_693433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693433 prefixEnd_693433 := by exact prefixLift 693433
  have htrace : WordTrace (prefixWord ++ tailWord_693433) baseStart_693433 baseEnd_693433 := by
    simpa [prefixWord, tailWord_693433, baseEnd_693433] using wordTrace_append hprefix tailTrace_693433
  have hstable : (prefixWord ++ tailWord_693433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693433).length < 2 ^ (prefixWord ++ tailWord_693433).sum := by decide
  have hdescent : baseEnd_693433 < baseStart_693433 := by decide
  rcases family_descends (prefixWord ++ tailWord_693433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693448 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_693448 : Nat := 118140960795 + 693448 * 2 ^ 59
def prefixEnd_693448 : Nat := 4983230072969 + 3 ^ 40 * 693448 * 2
def baseEnd_693448 : Nat := 237381421932738743473931

theorem tailTrace_693448 : CollatzResearch.WordTrace tailWord_693448 prefixEnd_693448 237381421932738743473931 := by
  unfold tailWord_693448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12646063195881901167348499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16861417594509201556464665 12646063195881901167348499)
  ·
    refine ⟨18969094793822851751022749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12646063195881901167348499 18969094793822851751022749)
    ·
      refine ⟨7113410547683569406633531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18969094793822851751022749 7113410547683569406633531)
      ·
        refine ⟨10670115821525354109950297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113410547683569406633531 10670115821525354109950297)
        ·
          refine ⟨8002586866144015582462723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10670115821525354109950297 8002586866144015582462723)
          ·
            refine ⟨12003880299216023373694085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8002586866144015582462723 12003880299216023373694085)
            ·
              refine ⟨2250727556103004382567641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12003880299216023373694085 2250727556103004382567641)
              ·
                refine ⟨1688045667077253286925731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250727556103004382567641 1688045667077253286925731)
                ·
                  refine ⟨2532068500615879930388597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688045667077253286925731 2532068500615879930388597)
                  ·
                    refine ⟨237381421932738743473931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2532068500615879930388597 237381421932738743473931)
                    ·
                      rfl

theorem cell22_693448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_693448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693448 prefixEnd_693448 := by exact prefixLift 693448
  have htrace : WordTrace (prefixWord ++ tailWord_693448) baseStart_693448 baseEnd_693448 := by
    simpa [prefixWord, tailWord_693448, baseEnd_693448] using wordTrace_append hprefix tailTrace_693448
  have hstable : (prefixWord ++ tailWord_693448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693448).length < 2 ^ (prefixWord ++ tailWord_693448).sum := by decide
  have hdescent : baseEnd_693448 < baseStart_693448 := by decide
  rcases family_descends (prefixWord ++ tailWord_693448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693450 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_693450 : Nat := 118140960795 + 693450 * 2 ^ 59
def prefixEnd_693450 : Nat := 4983230072969 + 3 ^ 40 * 693450 * 2
def baseEnd_693450 : Nat := 79127368857870468307975

theorem tailTrace_693450 : CollatzResearch.WordTrace tailWord_693450 prefixEnd_693450 79127368857870468307975 := by
  unfold tailWord_693450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323049834439139169067451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16861466225171037784179869 6323049834439139169067451)
  ·
    refine ⟨9484574751658708753601177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323049834439139169067451 9484574751658708753601177)
    ·
      refine ⟨7113431063744031565200883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9484574751658708753601177 7113431063744031565200883)
      ·
        refine ⟨10670146595616047347801325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113431063744031565200883 10670146595616047347801325)
        ·
          refine ⟨4001304973356017755425497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10670146595616047347801325 4001304973356017755425497)
          ·
            refine ⟨3000978730017013316569123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001304973356017755425497 3000978730017013316569123)
            ·
              refine ⟨4501468095025519974853685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000978730017013316569123 4501468095025519974853685)
              ·
                refine ⟨422012633908642497642533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4501468095025519974853685 422012633908642497642533)
                ·
                  refine ⟨79127368857870468307975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422012633908642497642533 79127368857870468307975)
                  ·
                    rfl

theorem cell22_693450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_693450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693450 prefixEnd_693450 := by exact prefixLift 693450
  have htrace : WordTrace (prefixWord ++ tailWord_693450) baseStart_693450 baseEnd_693450 := by
    simpa [prefixWord, tailWord_693450, baseEnd_693450] using wordTrace_append hprefix tailTrace_693450
  have hstable : (prefixWord ++ tailWord_693450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693450).length < 2 ^ (prefixWord ++ tailWord_693450).sum := by decide
  have hdescent : baseEnd_693450 < baseStart_693450 := by decide
  rcases family_descends (prefixWord ++ tailWord_693450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693463 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 2, 4]
def baseStart_693463 : Nat := 118140960795 + 693463 * 2 ^ 59
def prefixEnd_693463 : Nat := 4983230072969 + 3 ^ 40 * 693463 * 2
def baseEnd_693463 : Nat := 237386556739283704348885

theorem tailTrace_693463 : CollatzResearch.WordTrace tailWord_693463 prefixEnd_693463 237386556739283704348885 := by
  unfold tailWord_693463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25292673486709459896493043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16861782324472973264328695 25292673486709459896493043)
  ·
    refine ⟨37939010230064189844739565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25292673486709459896493043 37939010230064189844739565)
    ·
      refine ⟨14227128836274071191777337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37939010230064189844739565 14227128836274071191777337)
      ·
        refine ⟨10670346627205553393833003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14227128836274071191777337 10670346627205553393833003)
        ·
          refine ⟨16005519940808330090749505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670346627205553393833003 16005519940808330090749505)
          ·
            refine ⟨12004139955606247568062129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16005519940808330090749505 12004139955606247568062129)
            ·
              refine ⟨9003104966704685676046597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12004139955606247568062129 9003104966704685676046597)
              ·
                refine ⟨1688082181257128564258737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9003104966704685676046597 1688082181257128564258737)
                ·
                  refine ⟨1266061635942846423194053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1688082181257128564258737 1266061635942846423194053)
                  ·
                    refine ⟨237386556739283704348885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266061635942846423194053 237386556739283704348885)
                    ·
                      rfl

theorem cell22_693463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_693463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693463 prefixEnd_693463 := by exact prefixLift 693463
  have htrace : WordTrace (prefixWord ++ tailWord_693463) baseStart_693463 baseEnd_693463 := by
    simpa [prefixWord, tailWord_693463, baseEnd_693463] using wordTrace_append hprefix tailTrace_693463
  have hstable : (prefixWord ++ tailWord_693463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693463).length < 2 ^ (prefixWord ++ tailWord_693463).sum := by decide
  have hdescent : baseEnd_693463 < baseStart_693463 := by decide
  rcases family_descends (prefixWord ++ tailWord_693463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693540 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_693540 : Nat := 118140960795 + 693540 * 2 ^ 59
def prefixEnd_693540 : Nat := 4983230072969 + 3 ^ 40 * 693540 * 2
def baseEnd_693540 : Nat := 79137638470960390057883

theorem tailTrace_693540 : CollatzResearch.WordTrace tailWord_693540 prefixEnd_693540 79137638470960390057883 := by
  unfold tailWord_693540
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647740953715251023523037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16863654604953668031364049 12647740953715251023523037)
  ·
    refine ⟨4742902857643219133821139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12647740953715251023523037 4742902857643219133821139)
    ·
      refine ⟨7114354286464828700731709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4742902857643219133821139 7114354286464828700731709)
      ·
        refine ⟨2667882857424310762774391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7114354286464828700731709 2667882857424310762774391)
        ·
          refine ⟨4001824286136466144161587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667882857424310762774391 4001824286136466144161587)
          ·
            refine ⟨6002736429204699216242381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001824286136466144161587 6002736429204699216242381)
            ·
              refine ⟨2251026160951762206090893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6002736429204699216242381 2251026160951762206090893)
              ·
                refine ⟨844134810356910827284085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251026160951762206090893 844134810356910827284085)
                ·
                  refine ⟨79137638470960390057883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 844134810356910827284085 79137638470960390057883)
                  ·
                    rfl

theorem cell22_693540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_693540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693540 prefixEnd_693540 := by exact prefixLift 693540
  have htrace : WordTrace (prefixWord ++ tailWord_693540) baseStart_693540 baseEnd_693540 := by
    simpa [prefixWord, tailWord_693540, baseEnd_693540] using wordTrace_append hprefix tailTrace_693540
  have hstable : (prefixWord ++ tailWord_693540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693540).length < 2 ^ (prefixWord ++ tailWord_693540).sum := by decide
  have hdescent : baseEnd_693540 < baseStart_693540 := by decide
  rcases family_descends (prefixWord ++ tailWord_693540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693600 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_693600 : Nat := 118140960795 + 693600 * 2 ^ 59
def prefixEnd_693600 : Nat := 4983230072969 + 3 ^ 40 * 693600 * 2
def baseEnd_693600 : Nat := 237433454639061013673465

theorem tailTrace_693600 : CollatzResearch.WordTrace tailWord_693600 prefixEnd_693600 237433454639061013673465 := by
  unfold tailWord_693600
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648835143606566147115127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16865113524808754862820169 12648835143606566147115127)
  ·
    refine ⟨18973252715409849220672691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12648835143606566147115127 18973252715409849220672691)
    ·
      refine ⟨28459879073114773831009037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18973252715409849220672691 28459879073114773831009037)
      ·
        refine ⟨10672454652418040186628389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28459879073114773831009037 10672454652418040186628389)
        ·
          refine ⟨2001085247328382534992823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10672454652418040186628389 2001085247328382534992823)
          ·
            refine ⟨3001627870992573802489235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001085247328382534992823 3001627870992573802489235)
            ·
              refine ⟨4502441806488860703733853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001627870992573802489235 4502441806488860703733853)
              ·
                refine ⟨1688415677433322763900195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4502441806488860703733853 1688415677433322763900195)
                ·
                  refine ⟨2532623516149984145850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688415677433322763900195 2532623516149984145850293)
                  ·
                    refine ⟨237433454639061013673465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2532623516149984145850293 237433454639061013673465)
                    ·
                      rfl

theorem cell22_693600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_693600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693600 prefixEnd_693600 := by exact prefixLift 693600
  have htrace : WordTrace (prefixWord ++ tailWord_693600) baseStart_693600 baseEnd_693600 := by
    simpa [prefixWord, tailWord_693600, baseEnd_693600] using wordTrace_append hprefix tailTrace_693600
  have hstable : (prefixWord ++ tailWord_693600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693600).length < 2 ^ (prefixWord ++ tailWord_693600).sum := by decide
  have hdescent : baseEnd_693600 < baseStart_693600 := by decide
  rcases family_descends (prefixWord ++ tailWord_693600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693621 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_693621 : Nat := 118140960795 + 693621 * 2 ^ 59
def prefixEnd_693621 : Nat := 4983230072969 + 3 ^ 40 * 693621 * 2
def baseEnd_693621 : Nat := 237440643368223958898401

theorem tailTrace_693621 : CollatzResearch.WordTrace tailWord_693621 prefixEnd_693621 237440643368223958898401 := by
  unfold tailWord_693621
  simp only [CollatzResearch.WordTrace]
  refine ⟨25298436220137052880744717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16865624146758035253829811 25298436220137052880744717)
  ·
    refine ⟨9486913582551394830279269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25298436220137052880744717 9486913582551394830279269)
    ·
      refine ⟨1778796296728386530677363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9486913582551394830279269 1778796296728386530677363)
      ·
        refine ⟨2668194445092579796016045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778796296728386530677363 2668194445092579796016045)
        ·
          refine ⟨1000572916909717423506017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2668194445092579796016045 1000572916909717423506017)
          ·
            refine ⟨750429687682288067629513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000572916909717423506017 750429687682288067629513)
            ·
              refine ⟨562822265761716050722135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750429687682288067629513 562822265761716050722135)
              ·
                refine ⟨844233398642574076083203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562822265761716050722135 844233398642574076083203)
                ·
                  refine ⟨1266350097963861114124805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844233398642574076083203 1266350097963861114124805)
                  ·
                    refine ⟨237440643368223958898401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266350097963861114124805 237440643368223958898401)
                    ·
                      rfl

theorem cell22_693621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_693621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693621 prefixEnd_693621 := by exact prefixLift 693621
  have htrace : WordTrace (prefixWord ++ tailWord_693621) baseStart_693621 baseEnd_693621 := by
    simpa [prefixWord, tailWord_693621, baseEnd_693621] using wordTrace_append hprefix tailTrace_693621
  have hstable : (prefixWord ++ tailWord_693621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693621).length < 2 ^ (prefixWord ++ tailWord_693621).sum := by decide
  have hdescent : baseEnd_693621 < baseStart_693621 := by decide
  rcases family_descends (prefixWord ++ tailWord_693621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693698 : List Nat := [3, 5, 2, 1, 1, 1, 2, 7]
def baseStart_693698 : Nat := 118140960795 + 693698 * 2 ^ 59
def prefixEnd_693698 : Nat := 4983230072969 + 3 ^ 40 * 693698 * 2
def baseEnd_693698 : Nat := 26385222449091269413685

theorem tailTrace_693698 : CollatzResearch.WordTrace tailWord_693698 prefixEnd_693698 26385222449091269413685 := by
  unfold tailWord_693698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325311160214523757824437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16867496427238730020865165 6325311160214523757824437)
  ·
    refine ⟨592997921270111602296041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6325311160214523757824437 592997921270111602296041)
    ·
      refine ⟨444748440952583701722031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 592997921270111602296041 444748440952583701722031)
      ·
        refine ⟨667122661428875552583047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444748440952583701722031 667122661428875552583047)
        ·
          refine ⟨1000683992143313328874571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667122661428875552583047 1000683992143313328874571)
          ·
            refine ⟨1501025988214969993311857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000683992143313328874571 1501025988214969993311857)
            ·
              refine ⟨1125769491161227494983893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1501025988214969993311857 1125769491161227494983893)
              ·
                refine ⟨26385222449091269413685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1125769491161227494983893 26385222449091269413685)
                ·
                  rfl

theorem cell22_693698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_693698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693698 prefixEnd_693698 := by exact prefixLift 693698
  have htrace : WordTrace (prefixWord ++ tailWord_693698) baseStart_693698 baseEnd_693698 := by
    simpa [prefixWord, tailWord_693698, baseEnd_693698] using wordTrace_append hprefix tailTrace_693698
  have hstable : (prefixWord ++ tailWord_693698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693698).length < 2 ^ (prefixWord ++ tailWord_693698).sum := by decide
  have hdescent : baseEnd_693698 < baseStart_693698 := by decide
  rcases family_descends (prefixWord ++ tailWord_693698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693705 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_693705 : Nat := 118140960795 + 693705 * 2 ^ 59
def prefixEnd_693705 : Nat := 4983230072969 + 3 ^ 40 * 693705 * 2
def baseEnd_693705 : Nat := 237469398284875739798143

theorem tailTrace_693705 : CollatzResearch.WordTrace tailWord_693705 prefixEnd_693705 237469398284875739798143 := by
  unfold tailWord_693705
  simp only [CollatzResearch.WordTrace]
  refine ⟨25301499951832735226802569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16867666634555156817868379 25301499951832735226802569)
  ·
    refine ⟨18976124963874551420101927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25301499951832735226802569 18976124963874551420101927)
    ·
      refine ⟨28464187445811827130152891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18976124963874551420101927 28464187445811827130152891)
      ·
        refine ⟨42696281168717740695229337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28464187445811827130152891 42696281168717740695229337)
        ·
          refine ⟨32022210876538305521422003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42696281168717740695229337 32022210876538305521422003)
          ·
            refine ⟨48033316314807458282133005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32022210876538305521422003 48033316314807458282133005)
            ·
              refine ⟨18012493618052796855799877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48033316314807458282133005 18012493618052796855799877)
              ·
                refine ⟨3377342553384899410462477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18012493618052796855799877 3377342553384899410462477)
                ·
                  refine ⟨1266503457519337278923429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3377342553384899410462477 1266503457519337278923429)
                  ·
                    refine ⟨237469398284875739798143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266503457519337278923429 237469398284875739798143)
                    ·
                      rfl

theorem cell22_693705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_693705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693705 prefixEnd_693705 := by exact prefixLift 693705
  have htrace : WordTrace (prefixWord ++ tailWord_693705) baseStart_693705 baseEnd_693705 := by
    simpa [prefixWord, tailWord_693705, baseEnd_693705] using wordTrace_append hprefix tailTrace_693705
  have hstable : (prefixWord ++ tailWord_693705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693705).length < 2 ^ (prefixWord ++ tailWord_693705).sum := by decide
  have hdescent : baseEnd_693705 < baseStart_693705 := by decide
  rcases family_descends (prefixWord ++ tailWord_693705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693720 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_693720 : Nat := 118140960795 + 693720 * 2 ^ 59
def prefixEnd_693720 : Nat := 4983230072969 + 3 ^ 40 * 693720 * 2
def baseEnd_693720 : Nat := 79158177697140233557699

theorem tailTrace_693720 : CollatzResearch.WordTrace tailWord_693720 prefixEnd_693720 79158177697140233557699 := by
  unfold tailWord_693720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651023523389196394299307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16868031364518928525732409 12651023523389196394299307)
  ·
    refine ⟨18976535285083794591448961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12651023523389196394299307 18976535285083794591448961)
    ·
      refine ⟨14232401463812845943586721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18976535285083794591448961 14232401463812845943586721)
      ·
        refine ⟨10674301097859634457690041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14232401463812845943586721 10674301097859634457690041)
        ·
          refine ⟨8005725823394725843267531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10674301097859634457690041 8005725823394725843267531)
          ·
            refine ⟨12008588735092088764901297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8005725823394725843267531 12008588735092088764901297)
            ·
              refine ⟨9006441551319066573675973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12008588735092088764901297 9006441551319066573675973)
              ·
                refine ⟨1688707790872324982564245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9006441551319066573675973 1688707790872324982564245)
                ·
                  refine ⟨79158177697140233557699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1688707790872324982564245 79158177697140233557699)
                  ·
                    rfl

theorem cell22_693720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_693720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693720 prefixEnd_693720 := by exact prefixLift 693720
  have htrace : WordTrace (prefixWord ++ tailWord_693720) baseStart_693720 baseEnd_693720 := by
    simpa [prefixWord, tailWord_693720, baseEnd_693720] using wordTrace_append hprefix tailTrace_693720
  have hstable : (prefixWord ++ tailWord_693720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693720).length < 2 ^ (prefixWord ++ tailWord_693720).sum := by decide
  have hdescent : baseEnd_693720 < baseStart_693720 := by decide
  rcases family_descends (prefixWord ++ tailWord_693720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693722 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_693722 : Nat := 118140960795 + 693722 * 2 ^ 59
def prefixEnd_693722 : Nat := 4983230072969 + 3 ^ 40 * 693722 * 2
def baseEnd_693722 : Nat := 237475217732293362123091

theorem tailTrace_693722 : CollatzResearch.WordTrace tailWord_693722 prefixEnd_693722 237475217732293362123091 := by
  unfold tailWord_693722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325529998192786782542855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16868079995180764753447613 6325529998192786782542855)
  ·
    refine ⟨9488294997289180173814283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6325529998192786782542855 9488294997289180173814283)
    ·
      refine ⟨14232442495933770260721425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488294997289180173814283 14232442495933770260721425)
      ·
        refine ⟨10674331871950327695541069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14232442495933770260721425 10674331871950327695541069)
        ·
          refine ⟨4002874451981372885827901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10674331871950327695541069 4002874451981372885827901)
          ·
            refine ⟨1501077919493014832185463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4002874451981372885827901 1501077919493014832185463)
            ·
              refine ⟨2251616879239522248278195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501077919493014832185463 2251616879239522248278195)
              ·
                refine ⟨3377425318859283372417293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251616879239522248278195 3377425318859283372417293)
                ·
                  refine ⟨1266534494572231264656485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3377425318859283372417293 1266534494572231264656485)
                  ·
                    refine ⟨237475217732293362123091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266534494572231264656485 237475217732293362123091)
                    ·
                      rfl

theorem cell22_693722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_693722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693722 prefixEnd_693722 := by exact prefixLift 693722
  have htrace : WordTrace (prefixWord ++ tailWord_693722) baseStart_693722 baseEnd_693722 := by
    simpa [prefixWord, tailWord_693722, baseEnd_693722] using wordTrace_append hprefix tailTrace_693722
  have hstable : (prefixWord ++ tailWord_693722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693722).length < 2 ^ (prefixWord ++ tailWord_693722).sum := by decide
  have hdescent : baseEnd_693722 < baseStart_693722 := by decide
  rcases family_descends (prefixWord ++ tailWord_693722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693790 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_693790 : Nat := 118140960795 + 693790 * 2 ^ 59
def prefixEnd_693790 : Nat := 4983230072969 + 3 ^ 40 * 693790 * 2
def baseEnd_693790 : Nat := 237498495521963851422883

theorem tailTrace_693790 : CollatzResearch.WordTrace tailWord_693790 prefixEnd_693790 237498495521963851422883 := by
  unfold tailWord_693790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163075019565599342955853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16869733437683196495764549 3163075019565599342955853)
  ·
    refine ⟨1186153132337099753608445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3163075019565599342955853 1186153132337099753608445)
    ·
      refine ⟨444807424626412407603167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1186153132337099753608445 444807424626412407603167)
      ·
        refine ⟨667211136939618611404751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444807424626412407603167 667211136939618611404751)
        ·
          refine ⟨1000816705409427917107127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667211136939618611404751 1000816705409427917107127)
          ·
            refine ⟨1501225058114141875660691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000816705409427917107127 1501225058114141875660691)
            ·
              refine ⟨2251837587171212813491037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501225058114141875660691 2251837587171212813491037)
              ·
                refine ⟨844439095189204805059139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251837587171212813491037 844439095189204805059139)
                ·
                  refine ⟨1266658642783807207588709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844439095189204805059139 1266658642783807207588709)
                  ·
                    refine ⟨237498495521963851422883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266658642783807207588709 237498495521963851422883)
                    ·
                      rfl

theorem cell22_693790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_693790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693790 prefixEnd_693790 := by exact prefixLift 693790
  have htrace : WordTrace (prefixWord ++ tailWord_693790) baseStart_693790 baseEnd_693790 := by
    simpa [prefixWord, tailWord_693790, baseEnd_693790] using wordTrace_append hprefix tailTrace_693790
  have hstable : (prefixWord ++ tailWord_693790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693790).length < 2 ^ (prefixWord ++ tailWord_693790).sum := by decide
  have hdescent : baseEnd_693790 < baseStart_693790 := by decide
  rcases family_descends (prefixWord ++ tailWord_693790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693797 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_693797 : Nat := 118140960795 + 693797 * 2 ^ 59
def prefixEnd_693797 : Nat := 4983230072969 + 3 ^ 40 * 693797 * 2
def baseEnd_693797 : Nat := 237500891765018166497861

theorem tailTrace_693797 : CollatzResearch.WordTrace tailWord_693797 prefixEnd_693797 237500891765018166497861 := by
  unfold tailWord_693797
  simp only [CollatzResearch.WordTrace]
  refine ⟨25304855467499434939151645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16869903644999623292767763 25304855467499434939151645)
  ·
    refine ⟨9489320800312288102181867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25304855467499434939151645 9489320800312288102181867)
    ·
      refine ⟨14233981200468432153272801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9489320800312288102181867 14233981200468432153272801)
      ·
        refine ⟨10675485900351324114954601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14233981200468432153272801 10675485900351324114954601)
        ·
          refine ⟨8006614425263493086215951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10675485900351324114954601 8006614425263493086215951)
          ·
            refine ⟨12009921637895239629323927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006614425263493086215951 12009921637895239629323927)
            ·
              refine ⟨18014882456842859443985891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12009921637895239629323927 18014882456842859443985891)
              ·
                refine ⟨27022323685264289165978837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18014882456842859443985891 27022323685264289165978837)
                ·
                  refine ⟨633335711373381777327629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27022323685264289165978837 633335711373381777327629)
                  ·
                    refine ⟨237500891765018166497861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 633335711373381777327629 237500891765018166497861)
                    ·
                      rfl

theorem cell22_693797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_693797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693797 prefixEnd_693797 := by exact prefixLift 693797
  have htrace : WordTrace (prefixWord ++ tailWord_693797) baseStart_693797 baseEnd_693797 := by
    simpa [prefixWord, tailWord_693797, baseEnd_693797] using wordTrace_append hprefix tailTrace_693797
  have hstable : (prefixWord ++ tailWord_693797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693797).length < 2 ^ (prefixWord ++ tailWord_693797).sum := by decide
  have hdescent : baseEnd_693797 < baseStart_693797 := by decide
  rcases family_descends (prefixWord ++ tailWord_693797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693878 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_693878 : Nat := 118140960795 + 693878 * 2 ^ 59
def prefixEnd_693878 : Nat := 4983230072969 + 3 ^ 40 * 693878 * 2
def baseEnd_693878 : Nat := 79176206573453651740871

theorem tailTrace_693878 : CollatzResearch.WordTrace tailWord_693878 prefixEnd_693878 79176206573453651740871 := by
  unfold tailWord_693878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581738111262874110803143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16871873186803990515233525 1581738111262874110803143)
  ·
    refine ⟨2372607166894311166204715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581738111262874110803143 2372607166894311166204715)
    ·
      refine ⟨3558910750341466749307073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372607166894311166204715 3558910750341466749307073)
      ·
        refine ⟨2669183062756100061980305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3558910750341466749307073 2669183062756100061980305)
        ·
          refine ⟨2001887297067075046485229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669183062756100061980305 2001887297067075046485229)
          ·
            refine ⟨750707736400153142431961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2001887297067075046485229 750707736400153142431961)
            ·
              refine ⟨563030802300114856823971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750707736400153142431961 563030802300114856823971)
              ·
                refine ⟨844546203450172285235957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563030802300114856823971 844546203450172285235957)
                ·
                  refine ⟨79176206573453651740871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 844546203450172285235957 79176206573453651740871)
                  ·
                    rfl

theorem cell22_693878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_693878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693878 prefixEnd_693878 := by exact prefixLift 693878
  have htrace : WordTrace (prefixWord ++ tailWord_693878) baseStart_693878 baseEnd_693878 := by
    simpa [prefixWord, tailWord_693878, baseEnd_693878] using wordTrace_append hprefix tailTrace_693878
  have hstable : (prefixWord ++ tailWord_693878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693878).length < 2 ^ (prefixWord ++ tailWord_693878).sum := by decide
  have hdescent : baseEnd_693878 < baseStart_693878 := by decide
  rcases family_descends (prefixWord ++ tailWord_693878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693921 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_693921 : Nat := 118140960795 + 693921 * 2 ^ 59
def prefixEnd_693921 : Nat := 4983230072969 + 3 ^ 40 * 693921 * 2
def baseEnd_693921 : Nat := 237543339499123176397481

theorem tailTrace_693921 : CollatzResearch.WordTrace tailWord_693921 prefixEnd_693921 237543339499123176397481 := by
  unfold tailWord_693921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25309378119050204116665617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16872918746033469411110411 25309378119050204116665617)
  ·
    refine ⟨18982033589287653087499213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25309378119050204116665617 18982033589287653087499213)
    ·
      refine ⟨7118262595982869907812205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18982033589287653087499213 7118262595982869907812205)
      ·
        refine ⟨2669348473493576215429577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7118262595982869907812205 2669348473493576215429577)
        ·
          refine ⟨2002011355120182161572183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669348473493576215429577 2002011355120182161572183)
          ·
            refine ⟨3003017032680273242358275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002011355120182161572183 3003017032680273242358275)
            ·
              refine ⟨4504525549020409863537413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003017032680273242358275 4504525549020409863537413)
              ·
                refine ⟨844598540441326849413265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4504525549020409863537413 844598540441326849413265)
                ·
                  refine ⟨633448905330995137059949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 844598540441326849413265 633448905330995137059949)
                  ·
                    refine ⟨237543339499123176397481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 633448905330995137059949 237543339499123176397481)
                    ·
                      rfl

theorem cell22_693921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_693921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693921 prefixEnd_693921 := by exact prefixLift 693921
  have htrace : WordTrace (prefixWord ++ tailWord_693921) baseStart_693921 baseEnd_693921 := by
    simpa [prefixWord, tailWord_693921, baseEnd_693921] using wordTrace_append hprefix tailTrace_693921
  have hstable : (prefixWord ++ tailWord_693921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693921).length < 2 ^ (prefixWord ++ tailWord_693921).sum := by decide
  have hdescent : baseEnd_693921 < baseStart_693921 := by decide
  rcases family_descends (prefixWord ++ tailWord_693921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693994 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_693994 : Nat := 118140960795 + 693994 * 2 ^ 59
def prefixEnd_693994 : Nat := 4983230072969 + 3 ^ 40 * 693994 * 2
def baseEnd_693994 : Nat := 237568328890975319322257

theorem tailTrace_693994 : CollatzResearch.WordTrace tailWord_693994 prefixEnd_693994 237568328890975319322257 := by
  unfold tailWord_693994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328010161946434396018259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16874693765190491722715357 6328010161946434396018259)
  ·
    refine ⟨9492015242919651594027389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6328010161946434396018259 9492015242919651594027389)
    ·
      refine ⟨3559505716094869347760271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9492015242919651594027389 3559505716094869347760271)
      ·
        refine ⟨5339258574142304021640407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3559505716094869347760271 5339258574142304021640407)
        ·
          refine ⟨8008887861213456032460611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5339258574142304021640407 8008887861213456032460611)
          ·
            refine ⟨12013331791820184048690917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008887861213456032460611 12013331791820184048690917)
            ·
              refine ⟨2252499710966284509129547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12013331791820184048690917 2252499710966284509129547)
              ·
                refine ⟨3378749566449426763694321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252499710966284509129547 3378749566449426763694321)
                ·
                  refine ⟨2534062174837070072770741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3378749566449426763694321 2534062174837070072770741)
                  ·
                    refine ⟨237568328890975319322257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2534062174837070072770741 237568328890975319322257)
                    ·
                      rfl

theorem cell22_693994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_693994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_693994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_693994 prefixEnd_693994 := by exact prefixLift 693994
  have htrace : WordTrace (prefixWord ++ tailWord_693994) baseStart_693994 baseEnd_693994 := by
    simpa [prefixWord, tailWord_693994, baseEnd_693994] using wordTrace_append hprefix tailTrace_693994
  have hstable : (prefixWord ++ tailWord_693994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693994).length < 2 ^ (prefixWord ++ tailWord_693994).sum := by decide
  have hdescent : baseEnd_693994 < baseStart_693994 := by decide
  rcases family_descends (prefixWord ++ tailWord_693994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694026 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_694026 : Nat := 118140960795 + 694026 * 2 ^ 59
def prefixEnd_694026 : Nat := 4983230072969 + 3 ^ 40 * 694026 * 2
def baseEnd_694026 : Nat := 237579283144937902522159

theorem tailTrace_694026 : CollatzResearch.WordTrace tailWord_694026 prefixEnd_694026 237579283144937902522159 := by
  unfold tailWord_694026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328301945917451762309483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16875471855779871366158621 6328301945917451762309483)
  ·
    refine ⟨9492452918876177643464225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6328301945917451762309483 9492452918876177643464225)
    ·
      refine ⟨7119339689157133232598169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9492452918876177643464225 7119339689157133232598169)
      ·
        refine ⟨5339504766867849924448627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7119339689157133232598169 5339504766867849924448627)
        ·
          refine ⟨8009257150301774886672941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5339504766867849924448627 8009257150301774886672941)
          ·
            refine ⟨3003471431363165582502353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8009257150301774886672941 3003471431363165582502353)
            ·
              refine ⟨2252603573522374186876765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003471431363165582502353 2252603573522374186876765)
              ·
                refine ⟨844726340070890320078787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2252603573522374186876765 844726340070890320078787)
                ·
                  refine ⟨1267089510106335480118181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844726340070890320078787 1267089510106335480118181)
                  ·
                    refine ⟨237579283144937902522159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1267089510106335480118181 237579283144937902522159)
                    ·
                      rfl

theorem cell22_694026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_694026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694026 prefixEnd_694026 := by exact prefixLift 694026
  have htrace : WordTrace (prefixWord ++ tailWord_694026) baseStart_694026 baseEnd_694026 := by
    simpa [prefixWord, tailWord_694026, baseEnd_694026] using wordTrace_append hprefix tailTrace_694026
  have hstable : (prefixWord ++ tailWord_694026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694026).length < 2 ^ (prefixWord ++ tailWord_694026).sum := by decide
  have hdescent : baseEnd_694026 < baseStart_694026 := by decide
  rcases family_descends (prefixWord ++ tailWord_694026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694073 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_694073 : Nat := 118140960795 + 694073 * 2 ^ 59
def prefixEnd_694073 : Nat := 4983230072969 + 3 ^ 40 * 694073 * 2
def baseEnd_694073 : Nat := 237595372205445446597015

theorem tailTrace_694073 : CollatzResearch.WordTrace tailWord_694073 prefixEnd_694073 237595372205445446597015 := by
  unfold tailWord_694073
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314922014499534076198873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16876614676333022717465915 25314922014499534076198873)
  ·
    refine ⟨18986191510874650557149155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25314922014499534076198873 18986191510874650557149155)
    ·
      refine ⟨28479287266311975835723733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18986191510874650557149155 28479287266311975835723733)
      ·
        refine ⟨667483295304186933649775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28479287266311975835723733 667483295304186933649775)
        ·
          refine ⟨1001224942956280400474663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667483295304186933649775 1001224942956280400474663)
          ·
            refine ⟨1501837414434420600711995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001224942956280400474663 1501837414434420600711995)
            ·
              refine ⟨2252756121651630901067993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501837414434420600711995 2252756121651630901067993)
              ·
                refine ⟨1689567091238723175800995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252756121651630901067993 1689567091238723175800995)
                ·
                  refine ⟨2534350636858084763701493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689567091238723175800995 2534350636858084763701493)
                  ·
                    refine ⟨237595372205445446597015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2534350636858084763701493 237595372205445446597015)
                    ·
                      rfl

theorem cell22_694073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_694073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694073 prefixEnd_694073 := by exact prefixLift 694073
  have htrace : WordTrace (prefixWord ++ tailWord_694073) baseStart_694073 baseEnd_694073 := by
    simpa [prefixWord, tailWord_694073, baseEnd_694073] using wordTrace_append hprefix tailTrace_694073
  have hstable : (prefixWord ++ tailWord_694073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694073).length < 2 ^ (prefixWord ++ tailWord_694073).sum := by decide
  have hdescent : baseEnd_694073 < baseStart_694073 := by decide
  rcases family_descends (prefixWord ++ tailWord_694073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694092 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_694092 : Nat := 118140960795 + 694092 * 2 ^ 59
def prefixEnd_694092 : Nat := 4983230072969 + 3 ^ 40 * 694092 * 2
def baseEnd_694092 : Nat := 79200625431245243457319

theorem tailTrace_694092 : CollatzResearch.WordTrace tailWord_694092 prefixEnd_694092 79200625431245243457319 := by
  unfold tailWord_694092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657807500715350160570265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16877076667620466880760353 12657807500715350160570265)
  ·
    refine ⟨9493355625536512620427699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12657807500715350160570265 9493355625536512620427699)
    ·
      refine ⟨14240033438304768930641549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9493355625536512620427699 14240033438304768930641549)
      ·
        refine ⟨5340012539364288348990581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14240033438304768930641549 5340012539364288348990581)
        ·
          refine ⟨500626175565402032717867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5340012539364288348990581 500626175565402032717867)
          ·
            refine ⟨750939263348103049076801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500626175565402032717867 750939263348103049076801)
            ·
              refine ⟨563204447511077286807601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750939263348103049076801 563204447511077286807601)
              ·
                refine ⟨422403335633307965105701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563204447511077286807601 422403335633307965105701)
                ·
                  refine ⟨79200625431245243457319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422403335633307965105701 79200625431245243457319)
                  ·
                    rfl

theorem cell22_694092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_694092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694092 prefixEnd_694092 := by exact prefixLift 694092
  have htrace : WordTrace (prefixWord ++ tailWord_694092) baseStart_694092 baseEnd_694092 := by
    simpa [prefixWord, tailWord_694092, baseEnd_694092] using wordTrace_append hprefix tailTrace_694092
  have hstable : (prefixWord ++ tailWord_694092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694092).length < 2 ^ (prefixWord ++ tailWord_694092).sum := by decide
  have hdescent : baseEnd_694092 < baseStart_694092 := by decide
  rcases family_descends (prefixWord ++ tailWord_694092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694103 : List Nat := [1, 1, 3, 2, 6, 1, 1, 7]
def baseStart_694103 : Nat := 118140960795 + 694103 * 2 ^ 59
def prefixEnd_694103 : Nat := 4983230072969 + 3 ^ 40 * 694103 * 2
def baseEnd_694103 : Nat := 26400626868726152038547

theorem tailTrace_694103 : CollatzResearch.WordTrace tailWord_694103 prefixEnd_694103 26400626868726152038547 := by
  unfold tailWord_694103
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316016204390849199790963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16877344136260566133193975 25316016204390849199790963)
  ·
    refine ⟨37974024306586273799686445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25316016204390849199790963 37974024306586273799686445)
    ·
      refine ⟨14240259114969852674882417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37974024306586273799686445 14240259114969852674882417)
      ·
        refine ⟨10680194336227389506161813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14240259114969852674882417 10680194336227389506161813)
        ·
          refine ⟨500634109510658883101335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10680194336227389506161813 500634109510658883101335)
          ·
            refine ⟨750951164265988324652003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500634109510658883101335 750951164265988324652003)
            ·
              refine ⟨1126426746398982486978005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750951164265988324652003 1126426746398982486978005)
              ·
                refine ⟨26400626868726152038547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1126426746398982486978005 26400626868726152038547)
                ·
                  rfl

theorem cell22_694103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 7].length) (baseStart_694103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694103 prefixEnd_694103 := by exact prefixLift 694103
  have htrace : WordTrace (prefixWord ++ tailWord_694103) baseStart_694103 baseEnd_694103 := by
    simpa [prefixWord, tailWord_694103, baseEnd_694103] using wordTrace_append hprefix tailTrace_694103
  have hstable : (prefixWord ++ tailWord_694103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694103).length < 2 ^ (prefixWord ++ tailWord_694103).sum := by decide
  have hdescent : baseEnd_694103 < baseStart_694103 := by decide
  rcases family_descends (prefixWord ++ tailWord_694103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694122 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_694122 : Nat := 118140960795 + 694122 * 2 ^ 59
def prefixEnd_694122 : Nat := 4983230072969 + 3 ^ 40 * 694122 * 2
def baseEnd_694122 : Nat := 237612145906825652121865

theorem tailTrace_694122 : CollatzResearch.WordTrace tailWord_694122 prefixEnd_694122 237612145906825652121865 := by
  unfold tailWord_694122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329177297830503861183155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16877806127548010296488413 6329177297830503861183155)
  ·
    refine ⟨9493765946745755791774733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6329177297830503861183155 9493765946745755791774733)
    ·
      refine ⟨3560162230029658421915525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9493765946745755791774733 3560162230029658421915525)
      ·
        refine ⟨667530418130560954109161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3560162230029658421915525 667530418130560954109161)
        ·
          refine ⟨500647813597920715581871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667530418130560954109161 500647813597920715581871)
          ·
            refine ⟨750971720396881073372807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500647813597920715581871 750971720396881073372807)
            ·
              refine ⟨1126457580595321610059211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750971720396881073372807 1126457580595321610059211)
              ·
                refine ⟨1689686370892982415088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126457580595321610059211 1689686370892982415088817)
                ·
                  refine ⟨1267264778169736811316613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689686370892982415088817 1267264778169736811316613)
                  ·
                    refine ⟨237612145906825652121865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1267264778169736811316613 237612145906825652121865)
                    ·
                      rfl

theorem cell22_694122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_694122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694122 prefixEnd_694122 := by exact prefixLift 694122
  have htrace : WordTrace (prefixWord ++ tailWord_694122) baseStart_694122 baseEnd_694122 := by
    simpa [prefixWord, tailWord_694122, baseEnd_694122] using wordTrace_append hprefix tailTrace_694122
  have hstable : (prefixWord ++ tailWord_694122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694122).length < 2 ^ (prefixWord ++ tailWord_694122).sum := by decide
  have hdescent : baseEnd_694122 < baseStart_694122 := by decide
  rcases family_descends (prefixWord ++ tailWord_694122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694129 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_694129 : Nat := 118140960795 + 694129 * 2 ^ 59
def prefixEnd_694129 : Nat := 4983230072969 + 3 ^ 40 * 694129 * 2
def baseEnd_694129 : Nat := 237614542149879967196843

theorem tailTrace_694129 : CollatzResearch.WordTrace tailWord_694129 prefixEnd_694129 237614542149879967196843 := by
  unfold tailWord_694129
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316964502296655640237441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16877976334864437093491627 25316964502296655640237441)
  ·
    refine ⟨18987723376722491730178081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25316964502296655640237441 18987723376722491730178081)
    ·
      refine ⟨14240792532541868797633561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18987723376722491730178081 14240792532541868797633561)
      ·
        refine ⟨10680594399406401598225171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14240792532541868797633561 10680594399406401598225171)
        ·
          refine ⟨16020891599109602397337757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10680594399406401598225171 16020891599109602397337757)
          ·
            refine ⟨6007834349666100899001659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16020891599109602397337757 6007834349666100899001659)
            ·
              refine ⟨9011751524499151348502489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007834349666100899001659 9011751524499151348502489)
              ·
                refine ⟨6758813643374363511376867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9011751524499151348502489 6758813643374363511376867)
                ·
                  refine ⟨10138220465061545267065301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6758813643374363511376867 10138220465061545267065301)
                  ·
                    refine ⟨237614542149879967196843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10138220465061545267065301 237614542149879967196843)
                    ·
                      rfl

theorem cell22_694129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_694129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694129 prefixEnd_694129 := by exact prefixLift 694129
  have htrace : WordTrace (prefixWord ++ tailWord_694129) baseStart_694129 baseEnd_694129 := by
    simpa [prefixWord, tailWord_694129, baseEnd_694129] using wordTrace_append hprefix tailTrace_694129
  have hstable : (prefixWord ++ tailWord_694129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694129).length < 2 ^ (prefixWord ++ tailWord_694129).sum := by decide
  have hdescent : baseEnd_694129 < baseStart_694129 := by decide
  rcases family_descends (prefixWord ++ tailWord_694129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694191 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 6, 3]
def baseStart_694191 : Nat := 118140960795 + 694191 * 2 ^ 59
def prefixEnd_694191 : Nat := 4983230072969 + 3 ^ 40 * 694191 * 2
def baseEnd_694191 : Nat := 237635766016932472146653

theorem tailTrace_694191 : CollatzResearch.WordTrace tailWord_694191 prefixEnd_694191 237635766016932472146653 := by
  unfold tailWord_694191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25319225828072040228994427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16879483885381360152662951 25319225828072040228994427)
  ·
    refine ⟨37978838742108060343491641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25319225828072040228994427 37978838742108060343491641)
    ·
      refine ⟨28484129056581045257618731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37978838742108060343491641 28484129056581045257618731)
      ·
        refine ⟨42726193584871567886428097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28484129056581045257618731 42726193584871567886428097)
        ·
          refine ⟨32044645188653675914821073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42726193584871567886428097 32044645188653675914821073)
          ·
            refine ⟨24033483891490256936115805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32044645188653675914821073 24033483891490256936115805)
            ·
              refine ⟨9012556459308846351043427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24033483891490256936115805 9012556459308846351043427)
              ·
                refine ⟨13518834688963269526565141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012556459308846351043427 13518834688963269526565141)
                ·
                  refine ⟨633695376045153259057741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13518834688963269526565141 633695376045153259057741)
                  ·
                    refine ⟨237635766016932472146653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 633695376045153259057741 237635766016932472146653)
                    ·
                      rfl

theorem cell22_694191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_694191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694191 prefixEnd_694191 := by exact prefixLift 694191
  have htrace : WordTrace (prefixWord ++ tailWord_694191) baseStart_694191 baseEnd_694191 := by
    simpa [prefixWord, tailWord_694191, baseEnd_694191] using wordTrace_append hprefix tailTrace_694191
  have hstable : (prefixWord ++ tailWord_694191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694191).length < 2 ^ (prefixWord ++ tailWord_694191).sum := by decide
  have hdescent : baseEnd_694191 < baseStart_694191 := by decide
  rcases family_descends (prefixWord ++ tailWord_694191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694208 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_694208 : Nat := 118140960795 + 694208 * 2 ^ 59
def prefixEnd_694208 : Nat := 4983230072969 + 3 ^ 40 * 694208 * 2
def baseEnd_694208 : Nat := 237641585464350094471601

theorem tailTrace_694208 : CollatzResearch.WordTrace tailWord_694208 prefixEnd_694208 237641585464350094471601 := by
  unfold tailWord_694208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12659922934505226066181639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16879897246006968088242185 12659922934505226066181639)
  ·
    refine ⟨18989884401757839099272459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12659922934505226066181639 18989884401757839099272459)
    ·
      refine ⟨28484826602636758648908689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18989884401757839099272459 28484826602636758648908689)
      ·
        refine ⟨21363619951977568986681517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28484826602636758648908689 21363619951977568986681517)
        ·
          refine ⟨8011357481991588370005569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21363619951977568986681517 8011357481991588370005569)
          ·
            refine ⟨6008518111493691277504177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8011357481991588370005569 6008518111493691277504177)
            ·
              refine ⟨4506388583620268458128133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008518111493691277504177 4506388583620268458128133)
              ·
                refine ⟨844947859428800335899025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4506388583620268458128133 844947859428800335899025)
                ·
                  refine ⟨633710894571600251924269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 844947859428800335899025 633710894571600251924269)
                  ·
                    refine ⟨237641585464350094471601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 633710894571600251924269 237641585464350094471601)
                    ·
                      rfl

theorem cell22_694208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_694208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694208 prefixEnd_694208 := by exact prefixLift 694208
  have htrace : WordTrace (prefixWord ++ tailWord_694208) baseStart_694208 baseEnd_694208 := by
    simpa [prefixWord, tailWord_694208, baseEnd_694208] using wordTrace_append hprefix tailTrace_694208
  have hstable : (prefixWord ++ tailWord_694208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694208).length < 2 ^ (prefixWord ++ tailWord_694208).sum := by decide
  have hdescent : baseEnd_694208 < baseStart_694208 := by decide
  rcases family_descends (prefixWord ++ tailWord_694208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694373 : List Nat := [1, 3, 1, 3, 2, 4, 8]
def baseStart_694373 : Nat := 118140960795 + 694373 * 2 ^ 59
def prefixEnd_694373 : Nat := 4983230072969 + 3 ^ 40 * 694373 * 2
def baseEnd_694373 : Nat := 8803632160605357929485

theorem tailTrace_694373 : CollatzResearch.WordTrace tailWord_694373 prefixEnd_694373 8803632160605357929485 := by
  unfold tailWord_694373
  simp only [CollatzResearch.WordTrace]
  refine ⟨25325863913412685312119773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16883909275608456874746515 25325863913412685312119773)
  ·
    refine ⟨9497198967529756992044915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25325863913412685312119773 9497198967529756992044915)
    ·
      refine ⟨14245798451294635488067373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9497198967529756992044915 14245798451294635488067373)
      ·
        refine ⟨5342174419235488308025265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14245798451294635488067373 5342174419235488308025265)
        ·
          refine ⟨4006630814426616231018949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342174419235488308025265 4006630814426616231018949)
          ·
            refine ⟨751243277704990543316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4006630814426616231018949 751243277704990543316053)
            ·
              refine ⟨8803632160605357929485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 751243277704990543316053 8803632160605357929485)
              ·
                rfl

theorem cell22_694373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 8].length) (baseStart_694373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694373 prefixEnd_694373 := by exact prefixLift 694373
  have htrace : WordTrace (prefixWord ++ tailWord_694373) baseStart_694373 baseEnd_694373 := by
    simpa [prefixWord, tailWord_694373, baseEnd_694373] using wordTrace_append hprefix tailTrace_694373
  have hstable : (prefixWord ++ tailWord_694373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694373).length < 2 ^ (prefixWord ++ tailWord_694373).sum := by decide
  have hdescent : baseEnd_694373 < baseStart_694373 := by decide
  rcases family_descends (prefixWord ++ tailWord_694373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694390 : List Nat := [5, 1, 1, 2, 1, 3, 2, 7]
def baseStart_694390 : Nat := 118140960795 + 694390 * 2 ^ 59
def prefixEnd_694390 : Nat := 4983230072969 + 3 ^ 40 * 694390 * 2
def baseEnd_694390 : Nat := 26411543087084698491227

theorem tailTrace_694390 : CollatzResearch.WordTrace tailWord_694390 prefixEnd_694390 26411543087084698491227 := by
  unfold tailWord_694390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582905247146943575968039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16884322636234064810325749 1582905247146943575968039)
  ·
    refine ⟨2374357870720415363952059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582905247146943575968039 2374357870720415363952059)
    ·
      refine ⟨3561536806080623045928089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374357870720415363952059 3561536806080623045928089)
      ·
        refine ⟨2671152604560467284446067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3561536806080623045928089 2671152604560467284446067)
        ·
          refine ⟨4006728906840700926669101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671152604560467284446067 4006728906840700926669101)
          ·
            refine ⟨1502523340065262847500913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006728906840700926669101 1502523340065262847500913)
            ·
              refine ⟨1126892505048947135625685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502523340065262847500913 1126892505048947135625685)
              ·
                refine ⟨26411543087084698491227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1126892505048947135625685 26411543087084698491227)
                ·
                  rfl

theorem cell22_694390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_694390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694390 prefixEnd_694390 := by exact prefixLift 694390
  have htrace : WordTrace (prefixWord ++ tailWord_694390) baseStart_694390 baseEnd_694390 := by
    simpa [prefixWord, tailWord_694390, baseEnd_694390] using wordTrace_append hprefix tailTrace_694390
  have hstable : (prefixWord ++ tailWord_694390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694390).length < 2 ^ (prefixWord ++ tailWord_694390).sum := by decide
  have hdescent : baseEnd_694390 < baseStart_694390 := by decide
  rcases family_descends (prefixWord ++ tailWord_694390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694482 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_694482 : Nat := 118140960795 + 694482 * 2 ^ 59
def prefixEnd_694482 : Nat := 4983230072969 + 3 ^ 40 * 694482 * 2
def baseEnd_694482 : Nat := 237735381263904713120761

theorem tailTrace_694482 : CollatzResearch.WordTrace tailWord_694482 prefixEnd_694482 237735381263904713120761 := by
  unfold tailWord_694482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332459867504449231959425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16886559646678531285225133 6332459867504449231959425)
  ·
    refine ⟨4749344900628336923969569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6332459867504449231959425 4749344900628336923969569)
    ·
      refine ⟨3562008675471252692977177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4749344900628336923969569 3562008675471252692977177)
      ·
        refine ⟨2671506506603439519732883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3562008675471252692977177 2671506506603439519732883)
        ·
          refine ⟨4007259759905159279599325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671506506603439519732883 4007259759905159279599325)
          ·
            refine ⟨1502722409964434729849747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4007259759905159279599325 1502722409964434729849747)
            ·
              refine ⟨2254083614946652094774621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502722409964434729849747 2254083614946652094774621)
              ·
                refine ⟨845281355604994535540483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254083614946652094774621 845281355604994535540483)
                ·
                  refine ⟨1267922033407491803310725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845281355604994535540483 1267922033407491803310725)
                  ·
                    refine ⟨237735381263904713120761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1267922033407491803310725 237735381263904713120761)
                    ·
                      rfl

theorem cell22_694482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_694482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694482 prefixEnd_694482 := by exact prefixLift 694482
  have htrace : WordTrace (prefixWord ++ tailWord_694482) baseStart_694482 baseEnd_694482 := by
    simpa [prefixWord, tailWord_694482, baseEnd_694482] using wordTrace_append hprefix tailTrace_694482
  have hstable : (prefixWord ++ tailWord_694482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694482).length < 2 ^ (prefixWord ++ tailWord_694482).sum := by decide
  have hdescent : baseEnd_694482 < baseStart_694482 := by decide
  rcases family_descends (prefixWord ++ tailWord_694482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694508 : List Nat := [2, 2, 1, 1, 2, 3, 2, 9]
def baseStart_694508 : Nat := 118140960795 + 694508 * 2 ^ 59
def prefixEnd_694508 : Nat := 4983230072969 + 3 ^ 40 * 694508 * 2
def baseEnd_694508 : Nat := 26416031288361034663409

theorem tailTrace_694508 : CollatzResearch.WordTrace tailWord_694508 prefixEnd_694508 26416031288361034663409 := by
  unfold tailWord_694508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665393883961801684142089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16887191845282402245522785 12665393883961801684142089)
  ·
    refine ⟨9499045412971351263106567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12665393883961801684142089 9499045412971351263106567)
    ·
      refine ⟨14248568119457026894659851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499045412971351263106567 14248568119457026894659851)
      ·
        refine ⟨21372852179185540341989777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14248568119457026894659851 21372852179185540341989777)
        ·
          refine ⟨16029639134389155256492333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21372852179185540341989777 16029639134389155256492333)
          ·
            refine ⟨6011114675395933221184625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16029639134389155256492333 6011114675395933221184625)
            ·
              refine ⟨4508336006546949915888469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011114675395933221184625 4508336006546949915888469)
              ·
                refine ⟨26416031288361034663409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4508336006546949915888469 26416031288361034663409)
                ·
                  rfl

theorem cell22_694508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 9].length) (baseStart_694508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694508 prefixEnd_694508 := by exact prefixLift 694508
  have htrace : WordTrace (prefixWord ++ tailWord_694508) baseStart_694508 baseEnd_694508 := by
    simpa [prefixWord, tailWord_694508, baseEnd_694508] using wordTrace_append hprefix tailTrace_694508
  have hstable : (prefixWord ++ tailWord_694508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694508).length < 2 ^ (prefixWord ++ tailWord_694508).sum := by decide
  have hdescent : baseEnd_694508 < baseStart_694508 := by decide
  rcases family_descends (prefixWord ++ tailWord_694508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694615 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 6]
def baseStart_694615 : Nat := 118140960795 + 694615 * 2 ^ 59
def prefixEnd_694615 : Nat := 4983230072969 + 3 ^ 40 * 694615 * 2
def baseEnd_694615 : Nat := 79260303293978899848451

theorem tailTrace_694615 : CollatzResearch.WordTrace tailWord_694615 prefixEnd_694615 79260303293978899848451 := by
  unfold tailWord_694615
  simp only [CollatzResearch.WordTrace]
  refine ⟨25334690378535960642429299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16889793585690640428286199 25334690378535960642429299)
  ·
    refine ⟨38002035567803940963643949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25334690378535960642429299 38002035567803940963643949)
    ·
      refine ⟨14250763337926477861366481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38002035567803940963643949 14250763337926477861366481)
      ·
        refine ⟨10688072503444858396024861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14250763337926477861366481 10688072503444858396024861)
        ·
          refine ⟨4008027188791821898509323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10688072503444858396024861 4008027188791821898509323)
          ·
            refine ⟨6012040783187732847763985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008027188791821898509323 6012040783187732847763985)
            ·
              refine ⟨4509030587390799635822989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012040783187732847763985 4509030587390799635822989)
              ·
                refine ⟨1690886470271549863433621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4509030587390799635822989 1690886470271549863433621)
                ·
                  refine ⟨79260303293978899848451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1690886470271549863433621 79260303293978899848451)
                  ·
                    rfl

theorem cell22_694615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_694615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694615 prefixEnd_694615 := by exact prefixLift 694615
  have htrace : WordTrace (prefixWord ++ tailWord_694615) baseStart_694615 baseEnd_694615 := by
    simpa [prefixWord, tailWord_694615, baseEnd_694615] using wordTrace_append hprefix tailTrace_694615
  have hstable : (prefixWord ++ tailWord_694615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694615).length < 2 ^ (prefixWord ++ tailWord_694615).sum := by decide
  have hdescent : baseEnd_694615 < baseStart_694615 := by decide
  rcases family_descends (prefixWord ++ tailWord_694615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694632 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_694632 : Nat := 118140960795 + 694632 * 2 ^ 59
def prefixEnd_694632 : Nat := 4983230072969 + 3 ^ 40 * 694632 * 2
def baseEnd_694632 : Nat := 79262243109784773956767

theorem tailTrace_694632 : CollatzResearch.WordTrace tailWord_694632 prefixEnd_694632 79262243109784773956767 := by
  unfold tailWord_694632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667655209737186272899075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16890206946316248363865433 12667655209737186272899075)
  ·
    refine ⟨19001482814605779409348613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12667655209737186272899075 19001482814605779409348613)
    ·
      refine ⟨3562778027738583639252865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19001482814605779409348613 3562778027738583639252865)
      ·
        refine ⟨2672083520803937729439649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3562778027738583639252865 2672083520803937729439649)
        ·
          refine ⟨2004062640602953297079737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672083520803937729439649 2004062640602953297079737)
          ·
            refine ⟨1503046980452214972809803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004062640602953297079737 1503046980452214972809803)
            ·
              refine ⟨2254570470678322459214705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503046980452214972809803 2254570470678322459214705)
              ·
                refine ⟨1690927853008741844411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254570470678322459214705 1690927853008741844411029)
                ·
                  refine ⟨79262243109784773956767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1690927853008741844411029 79262243109784773956767)
                  ·
                    rfl

theorem cell22_694632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_694632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694632 prefixEnd_694632 := by exact prefixLift 694632
  have htrace : WordTrace (prefixWord ++ tailWord_694632) baseStart_694632 baseEnd_694632 := by
    simpa [prefixWord, tailWord_694632, baseEnd_694632] using wordTrace_append hprefix tailTrace_694632
  have hstable : (prefixWord ++ tailWord_694632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694632).length < 2 ^ (prefixWord ++ tailWord_694632).sum := by decide
  have hdescent : baseEnd_694632 < baseStart_694632 := by decide
  rcases family_descends (prefixWord ++ tailWord_694632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694660 : List Nat := [2, 3, 2, 1, 1, 2, 11]
def baseStart_694660 : Nat := 118140960795 + 694660 * 2 ^ 59
def prefixEnd_694660 : Nat := 4983230072969 + 3 ^ 40 * 694660 * 2
def baseEnd_694660 : Nat := 8807270900058206747045

theorem tailTrace_694660 : CollatzResearch.WordTrace tailWord_694660 prefixEnd_694660 8807270900058206747045 := by
  unfold tailWord_694660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12668165831686466663908717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16890887775581955551878289 12668165831686466663908717)
  ·
    refine ⟨4750562186882424998965769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12668165831686466663908717 4750562186882424998965769)
    ·
      refine ⟨3562921640161818749224327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4750562186882424998965769 3562921640161818749224327)
      ·
        refine ⟨5344382460242728123836491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562921640161818749224327 5344382460242728123836491)
        ·
          refine ⟨8016573690364092185754737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344382460242728123836491 8016573690364092185754737)
          ·
            refine ⟨6012430267773069139316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8016573690364092185754737 6012430267773069139316053)
            ·
              refine ⟨8807270900058206747045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6012430267773069139316053 8807270900058206747045)
              ·
                rfl

theorem cell22_694660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 11].length) (baseStart_694660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694660 prefixEnd_694660 := by exact prefixLift 694660
  have htrace : WordTrace (prefixWord ++ tailWord_694660) baseStart_694660 baseEnd_694660 := by
    simpa [prefixWord, tailWord_694660, baseEnd_694660] using wordTrace_append hprefix tailTrace_694660
  have hstable : (prefixWord ++ tailWord_694660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694660).length < 2 ^ (prefixWord ++ tailWord_694660).sum := by decide
  have hdescent : baseEnd_694660 < baseStart_694660 := by decide
  rcases family_descends (prefixWord ++ tailWord_694660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694735 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_694735 : Nat := 118140960795 + 694735 * 2 ^ 59
def prefixEnd_694735 : Nat := 4983230072969 + 3 ^ 40 * 694735 * 2
def baseEnd_694735 : Nat := 237821988334296386544985

theorem tailTrace_694735 : CollatzResearch.WordTrace tailWord_694735 prefixEnd_694735 237821988334296386544985 := by
  unfold tailWord_694735
  simp only [CollatzResearch.WordTrace]
  refine ⟨25339067138101221136797659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16892711425400814091198439 25339067138101221136797659)
  ·
    refine ⟨38008600707151831705196489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25339067138101221136797659 38008600707151831705196489)
    ·
      refine ⟨28506450530363873778897367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38008600707151831705196489 28506450530363873778897367)
      ·
        refine ⟨42759675795545810668346051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28506450530363873778897367 42759675795545810668346051)
        ·
          refine ⟨64139513693318716002519077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42759675795545810668346051 64139513693318716002519077)
          ·
            refine ⟨12026158817497259250472327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64139513693318716002519077 12026158817497259250472327)
            ·
              refine ⟨18039238226245888875708491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12026158817497259250472327 18039238226245888875708491)
              ·
                refine ⟨27058857339368833313562737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18039238226245888875708491 27058857339368833313562737)
                ·
                  refine ⟨20294143004526624985172053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27058857339368833313562737 20294143004526624985172053)
                  ·
                    refine ⟨237821988334296386544985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20294143004526624985172053 237821988334296386544985)
                    ·
                      rfl

theorem cell22_694735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_694735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694735 prefixEnd_694735 := by exact prefixLift 694735
  have htrace : WordTrace (prefixWord ++ tailWord_694735) baseStart_694735 baseEnd_694735 := by
    simpa [prefixWord, tailWord_694735, baseEnd_694735] using wordTrace_append hprefix tailTrace_694735
  have hstable : (prefixWord ++ tailWord_694735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694735).length < 2 ^ (prefixWord ++ tailWord_694735).sum := by decide
  have hdescent : baseEnd_694735 < baseStart_694735 := by decide
  rcases family_descends (prefixWord ++ tailWord_694735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694752 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_694752 : Nat := 118140960795 + 694752 * 2 ^ 59
def prefixEnd_694752 : Nat := 4983230072969 + 3 ^ 40 * 694752 * 2
def baseEnd_694752 : Nat := 237827807781714008869933

theorem tailTrace_694752 : CollatzResearch.WordTrace tailWord_694752 prefixEnd_694752 237827807781714008869933 := by
  unfold tailWord_694752
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669843589519816520083255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16893124786026422026777673 12669843589519816520083255)
  ·
    refine ⟨19004765384279724780124883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12669843589519816520083255 19004765384279724780124883)
    ·
      refine ⟨28507148076419587170187325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19004765384279724780124883 28507148076419587170187325)
      ·
        refine ⟨10690180528657345188820247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28507148076419587170187325 10690180528657345188820247)
        ·
          refine ⟨16035270792986017783230371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690180528657345188820247 16035270792986017783230371)
          ·
            refine ⟨24052906189479026674845557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16035270792986017783230371 24052906189479026674845557)
            ·
              refine ⟨2254959955263658750766771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24052906189479026674845557 2254959955263658750766771)
              ·
                refine ⟨3382439932895488126150157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254959955263658750766771 3382439932895488126150157)
                ·
                  refine ⟨1268414974835808047306309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3382439932895488126150157 1268414974835808047306309)
                  ·
                    refine ⟨237827807781714008869933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1268414974835808047306309 237827807781714008869933)
                    ·
                      rfl

theorem cell22_694752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_694752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694752 prefixEnd_694752 := by exact prefixLift 694752
  have htrace : WordTrace (prefixWord ++ tailWord_694752) baseStart_694752 baseEnd_694752 := by
    simpa [prefixWord, tailWord_694752, baseEnd_694752] using wordTrace_append hprefix tailTrace_694752
  have hstable : (prefixWord ++ tailWord_694752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694752).length < 2 ^ (prefixWord ++ tailWord_694752).sum := by decide
  have hdescent : baseEnd_694752 < baseStart_694752 := by decide
  rcases family_descends (prefixWord ++ tailWord_694752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694820 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_694820 : Nat := 118140960795 + 694820 * 2 ^ 59
def prefixEnd_694820 : Nat := 4983230072969 + 3 ^ 40 * 694820 * 2
def baseEnd_694820 : Nat := 237851085571384498169725

theorem tailTrace_694820 : CollatzResearch.WordTrace tailWord_694820 prefixEnd_694820 237851085571384498169725 := by
  unfold tailWord_694820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671083671396640326820957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16894778228528853769094609 12671083671396640326820957)
  ·
    refine ⟨4751656376773740122557859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12671083671396640326820957 4751656376773740122557859)
    ·
      refine ⟨7127484565160610183836789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751656376773740122557859 7127484565160610183836789)
      ·
        refine ⟨668201677983807204734699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7127484565160610183836789 668201677983807204734699)
        ·
          refine ⟨1002302516975710807102049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668201677983807204734699 1002302516975710807102049)
          ·
            refine ⟨751726887731783105326537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002302516975710807102049 751726887731783105326537)
            ·
              refine ⟨563795165798837328994903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751726887731783105326537 563795165798837328994903)
              ·
                refine ⟨845692748698255993492355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563795165798837328994903 845692748698255993492355)
                ·
                  refine ⟨1268539123047383990238533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845692748698255993492355 1268539123047383990238533)
                  ·
                    refine ⟨237851085571384498169725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1268539123047383990238533 237851085571384498169725)
                    ·
                      rfl

theorem cell22_694820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_694820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694820 prefixEnd_694820 := by exact prefixLift 694820
  have htrace : WordTrace (prefixWord ++ tailWord_694820) baseStart_694820 baseEnd_694820 := by
    simpa [prefixWord, tailWord_694820, baseEnd_694820] using wordTrace_append hprefix tailTrace_694820
  have hstable : (prefixWord ++ tailWord_694820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694820).length < 2 ^ (prefixWord ++ tailWord_694820).sum := by decide
  have hdescent : baseEnd_694820 < baseStart_694820 := by decide
  rcases family_descends (prefixWord ++ tailWord_694820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694872 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_694872 : Nat := 118140960795 + 694872 * 2 ^ 59
def prefixEnd_694872 : Nat := 4983230072969 + 3 ^ 40 * 694872 * 2
def baseEnd_694872 : Nat := 237868886234073695869565

theorem tailTrace_694872 : CollatzResearch.WordTrace tailWord_694872 prefixEnd_694872 237868886234073695869565 := by
  unfold tailWord_694872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672031969302446767267435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16896042625736595689689913 12672031969302446767267435)
  ·
    refine ⟨19008047953953670150901153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12672031969302446767267435 19008047953953670150901153)
    ·
      refine ⟨14256035965465252613175865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19008047953953670150901153 14256035965465252613175865)
      ·
        refine ⟨10692026974098939459881899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14256035965465252613175865 10692026974098939459881899)
        ·
          refine ⟨16038040461148409189822849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10692026974098939459881899 16038040461148409189822849)
          ·
            refine ⟨12028530345861306892367137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16038040461148409189822849 12028530345861306892367137)
            ·
              refine ⟨9021397759395980169275353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12028530345861306892367137 9021397759395980169275353)
              ·
                refine ⟨6766048319546985126956515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9021397759395980169275353 6766048319546985126956515)
                ·
                  refine ⟨10149072479320477690434773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766048319546985126956515 10149072479320477690434773)
                  ·
                    refine ⟨237868886234073695869565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10149072479320477690434773 237868886234073695869565)
                    ·
                      rfl

theorem cell22_694872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_694872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694872 prefixEnd_694872 := by exact prefixLift 694872
  have htrace : WordTrace (prefixWord ++ tailWord_694872) baseStart_694872 baseEnd_694872 := by
    simpa [prefixWord, tailWord_694872, baseEnd_694872] using wordTrace_append hprefix tailTrace_694872
  have hstable : (prefixWord ++ tailWord_694872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694872).length < 2 ^ (prefixWord ++ tailWord_694872).sum := by decide
  have hdescent : baseEnd_694872 < baseStart_694872 := by decide
  rcases family_descends (prefixWord ++ tailWord_694872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694936 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_694936 : Nat := 118140960795 + 694936 * 2 ^ 59
def prefixEnd_694936 : Nat := 4983230072969 + 3 ^ 40 * 694936 * 2
def baseEnd_694936 : Nat := 79296931580666287423123

theorem tailTrace_694936 : CollatzResearch.WordTrace tailWord_694936 prefixEnd_694936 79296931580666287423123 := by
  unfold tailWord_694936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12673199105186516232432331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16897598806915354976576441 12673199105186516232432331)
  ·
    refine ⟨19009798657779774348648497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12673199105186516232432331 19009798657779774348648497)
    ·
      refine ⟨14257348993334830761486373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19009798657779774348648497 14257348993334830761486373)
      ·
        refine ⟨2673252936250280767778695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14257348993334830761486373 2673252936250280767778695)
        ·
          refine ⟨4009879404375421151668043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673252936250280767778695 4009879404375421151668043)
          ·
            refine ⟨6014819106563131727502065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009879404375421151668043 6014819106563131727502065)
            ·
              refine ⟨4511114329922348795626549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014819106563131727502065 4511114329922348795626549)
              ·
                refine ⟨422916968430220199589989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4511114329922348795626549 422916968430220199589989)
                ·
                  refine ⟨79296931580666287423123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422916968430220199589989 79296931580666287423123)
                  ·
                    rfl

theorem cell22_694936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_694936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694936 prefixEnd_694936 := by exact prefixLift 694936
  have htrace : WordTrace (prefixWord ++ tailWord_694936) baseStart_694936 baseEnd_694936 := by
    simpa [prefixWord, tailWord_694936, baseEnd_694936] using wordTrace_append hprefix tailTrace_694936
  have hstable : (prefixWord ++ tailWord_694936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694936).length < 2 ^ (prefixWord ++ tailWord_694936).sum := by decide
  have hdescent : baseEnd_694936 < baseStart_694936 := by decide
  rcases family_descends (prefixWord ++ tailWord_694936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694989 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_694989 : Nat := 118140960795 + 694989 * 2 ^ 59
def prefixEnd_694989 : Nat := 4983230072969 + 3 ^ 40 * 694989 * 2
def baseEnd_694989 : Nat := 237908937725124390694207

theorem tailTrace_694989 : CollatzResearch.WordTrace tailWord_694989 prefixEnd_694989 237908937725124390694207 := by
  unfold tailWord_694989
  simp only [CollatzResearch.WordTrace]
  refine ⟨25348331279181022516544021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16898887519454015011029347 25348331279181022516544021)
  ·
    refine ⟨1188203028711610430463001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25348331279181022516544021 1188203028711610430463001)
    ·
      refine ⟨891152271533707822847251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1188203028711610430463001 891152271533707822847251)
      ·
        refine ⟨1336728407300561734270877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891152271533707822847251 1336728407300561734270877)
        ·
          refine ⟨501273152737710650351579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1336728407300561734270877 501273152737710650351579)
          ·
            refine ⟨751909729106565975527369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501273152737710650351579 751909729106565975527369)
            ·
              refine ⟨563932296829924481645527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751909729106565975527369 563932296829924481645527)
              ·
                refine ⟨845898445244886722468291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563932296829924481645527 845898445244886722468291)
                ·
                  refine ⟨1268847667867330083702437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845898445244886722468291 1268847667867330083702437)
                  ·
                    refine ⟨237908937725124390694207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1268847667867330083702437 237908937725124390694207)
                    ·
                      rfl

theorem cell22_694989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_694989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_694989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_694989 prefixEnd_694989 := by exact prefixLift 694989
  have htrace : WordTrace (prefixWord ++ tailWord_694989) baseStart_694989 baseEnd_694989 := by
    simpa [prefixWord, tailWord_694989, baseEnd_694989] using wordTrace_append hprefix tailTrace_694989
  have hstable : (prefixWord ++ tailWord_694989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694989).length < 2 ^ (prefixWord ++ tailWord_694989).sum := by decide
  have hdescent : baseEnd_694989 < baseStart_694989 := by decide
  rcases family_descends (prefixWord ++ tailWord_694989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695013 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_695013 : Nat := 118140960795 + 695013 * 2 ^ 59
def prefixEnd_695013 : Nat := 4983230072969 + 3 ^ 40 * 695013 * 2
def baseEnd_695013 : Nat := 237917153415596328094133

theorem tailTrace_695013 : CollatzResearch.WordTrace tailWord_695013 prefixEnd_695013 237917153415596328094133 := by
  unfold tailWord_695013
  simp only [CollatzResearch.WordTrace]
  refine ⟨25349206631094074615417693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16899471087396049743611795 25349206631094074615417693)
  ·
    refine ⟨9505952486660277980781635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25349206631094074615417693 9505952486660277980781635)
    ·
      refine ⟨14258928729990416971172453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9505952486660277980781635 14258928729990416971172453)
      ·
        refine ⟨2673549136873203182094835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14258928729990416971172453 2673549136873203182094835)
        ·
          refine ⟨4010323705309804773142253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673549136873203182094835 4010323705309804773142253)
          ·
            refine ⟨1503871389491176789928345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4010323705309804773142253 1503871389491176789928345)
            ·
              refine ⟨1127903542118382592446259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1503871389491176789928345 1127903542118382592446259)
              ·
                refine ⟨1691855313177573888669389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127903542118382592446259 1691855313177573888669389)
                ·
                  refine ⟨634445742441590208251021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1691855313177573888669389 634445742441590208251021)
                  ·
                    refine ⟨237917153415596328094133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634445742441590208251021 237917153415596328094133)
                    ·
                      rfl

theorem cell22_695013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_695013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695013 prefixEnd_695013 := by exact prefixLift 695013
  have htrace : WordTrace (prefixWord ++ tailWord_695013) baseStart_695013 baseEnd_695013 := by
    simpa [prefixWord, tailWord_695013, baseEnd_695013] using wordTrace_append hprefix tailTrace_695013
  have hstable : (prefixWord ++ tailWord_695013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695013).length < 2 ^ (prefixWord ++ tailWord_695013).sum := by decide
  have hdescent : baseEnd_695013 < baseStart_695013 := by decide
  rcases family_descends (prefixWord ++ tailWord_695013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695024 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_695024 : Nat := 118140960795 + 695024 * 2 ^ 59
def prefixEnd_695024 : Nat := 4983230072969 + 3 ^ 40 * 695024 * 2
def baseEnd_695024 : Nat := 237920918940395966069099

theorem tailTrace_695024 : CollatzResearch.WordTrace tailWord_695024 prefixEnd_695024 237920918940395966069099 := by
  unfold tailWord_695024
  simp only [CollatzResearch.WordTrace]
  refine ⟨12674803917027111747034063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16899738556036148996045417 12674803917027111747034063)
  ·
    refine ⟨19012205875540667620551095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12674803917027111747034063 19012205875540667620551095)
    ·
      refine ⟨28518308813311001430826643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19012205875540667620551095 28518308813311001430826643)
      ·
        refine ⟨42777463219966502146239965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28518308813311001430826643 42777463219966502146239965)
        ·
          refine ⟨16041548707487438304839987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42777463219966502146239965 16041548707487438304839987)
          ·
            refine ⟨24062323061231157457259981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16041548707487438304839987 24062323061231157457259981)
            ·
              refine ⟨9023371147961684046472493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24062323061231157457259981 9023371147961684046472493)
              ·
                refine ⟨3383764180485631517427185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9023371147961684046472493 3383764180485631517427185)
                ·
                  refine ⟨2537823135364223638070389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383764180485631517427185 2537823135364223638070389)
                  ·
                    refine ⟨237920918940395966069099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2537823135364223638070389 237920918940395966069099)
                    ·
                      rfl

theorem cell22_695024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_695024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695024 prefixEnd_695024 := by exact prefixLift 695024
  have htrace : WordTrace (prefixWord ++ tailWord_695024) baseStart_695024 baseEnd_695024 := by
    simpa [prefixWord, tailWord_695024, baseEnd_695024] using wordTrace_append hprefix tailTrace_695024
  have hstable : (prefixWord ++ tailWord_695024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695024).length < 2 ^ (prefixWord ++ tailWord_695024).sum := by decide
  have hdescent : baseEnd_695024 < baseStart_695024 := by decide
  rcases family_descends (prefixWord ++ tailWord_695024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695047 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 1, 3]
def baseStart_695047 : Nat := 118140960795 + 695047 * 2 ^ 59
def prefixEnd_695047 : Nat := 4983230072969 + 3 ^ 40 * 695047 * 2
def baseEnd_695047 : Nat := 237928792310431572744029

theorem tailTrace_695047 : CollatzResearch.WordTrace tailWord_695047 prefixEnd_695047 237928792310431572744029 := by
  unfold tailWord_695047
  simp only [CollatzResearch.WordTrace]
  refine ⟨25350446712970898422155395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16900297808647265614770263 25350446712970898422155395)
  ·
    refine ⟨38025670069456347633233093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25350446712970898422155395 38025670069456347633233093)
    ·
      refine ⟨7129813138023065181231205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38025670069456347633233093 7129813138023065181231205)
      ·
        refine ⟨1336839963379324721480851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7129813138023065181231205 1336839963379324721480851)
        ·
          refine ⟨2005259945068987082221277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336839963379324721480851 2005259945068987082221277)
          ·
            refine ⟨751972479400870155832979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2005259945068987082221277 751972479400870155832979)
            ·
              refine ⟨1127958719101305233749469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751972479400870155832979 1127958719101305233749469)
              ·
                refine ⟨422984519662989462656051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127958719101305233749469 422984519662989462656051)
                ·
                  refine ⟨634476779494484193984077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422984519662989462656051 634476779494484193984077)
                  ·
                    refine ⟨237928792310431572744029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634476779494484193984077 237928792310431572744029)
                    ·
                      rfl

theorem cell22_695047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_695047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695047 prefixEnd_695047 := by exact prefixLift 695047
  have htrace : WordTrace (prefixWord ++ tailWord_695047) baseStart_695047 baseEnd_695047 := by
    simpa [prefixWord, tailWord_695047, baseEnd_695047] using wordTrace_append hprefix tailTrace_695047
  have hstable : (prefixWord ++ tailWord_695047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695047).length < 2 ^ (prefixWord ++ tailWord_695047).sum := by decide
  have hdescent : baseEnd_695047 < baseStart_695047 := by decide
  rcases family_descends (prefixWord ++ tailWord_695047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695071 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 6]
def baseStart_695071 : Nat := 118140960795 + 695071 * 2 ^ 59
def prefixEnd_695071 : Nat := 4983230072969 + 3 ^ 40 * 695071 * 2
def baseEnd_695071 : Nat := 79312336000301170047985

theorem tailTrace_695071 : CollatzResearch.WordTrace tailWord_695071 prefixEnd_695071 79312336000301170047985 := by
  unfold tailWord_695071
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351322064883950521029067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16900881376589300347352711 25351322064883950521029067)
  ·
    refine ⟨38026983097325925781543601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25351322064883950521029067 38026983097325925781543601)
    ·
      refine ⟨28520237322994444336157701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38026983097325925781543601 28520237322994444336157701)
      ·
        refine ⟨5347544498061458313029569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28520237322994444336157701 5347544498061458313029569)
        ·
          refine ⟨4010658373546093734772177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5347544498061458313029569 4010658373546093734772177)
          ·
            refine ⟨3007993780159570301079133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4010658373546093734772177 3007993780159570301079133)
            ·
              refine ⟨1127997667559838862904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3007993780159570301079133 1127997667559838862904675)
              ·
                refine ⟨1691996501339758294357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127997667559838862904675 1691996501339758294357013)
                ·
                  refine ⟨79312336000301170047985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1691996501339758294357013 79312336000301170047985)
                  ·
                    rfl

theorem cell22_695071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 6].length) (baseStart_695071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695071 prefixEnd_695071 := by exact prefixLift 695071
  have htrace : WordTrace (prefixWord ++ tailWord_695071) baseStart_695071 baseEnd_695071 := by
    simpa [prefixWord, tailWord_695071, baseEnd_695071] using wordTrace_append hprefix tailTrace_695071
  have hstable : (prefixWord ++ tailWord_695071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695071).length < 2 ^ (prefixWord ++ tailWord_695071).sum := by decide
  have hdescent : baseEnd_695071 < baseStart_695071 := by decide
  rcases family_descends (prefixWord ++ tailWord_695071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695148 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_695148 : Nat := 118140960795 + 695148 * 2 ^ 59
def prefixEnd_695148 : Nat := 4983230072969 + 3 ^ 40 * 695148 * 2
def baseEnd_695148 : Nat := 237963366674500975968719

theorem tailTrace_695148 : CollatzResearch.WordTrace tailWord_695148 prefixEnd_695148 237963366674500975968719 := by
  unfold tailWord_695148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677065242802496335791049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16902753657069995114388065 12677065242802496335791049)
  ·
    refine ⟨9507798932101872251843287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12677065242802496335791049 9507798932101872251843287)
    ·
      refine ⟨14261698398152808377764931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9507798932101872251843287 14261698398152808377764931)
      ·
        refine ⟨21392547597229212566647397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261698398152808377764931 21392547597229212566647397)
        ·
          refine ⟨4011102674480477356246387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21392547597229212566647397 4011102674480477356246387)
          ·
            refine ⟨6016654011720716034369581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011102674480477356246387 6016654011720716034369581)
            ·
              refine ⟨2256245254395268512888593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6016654011720716034369581 2256245254395268512888593)
              ·
                refine ⟨1692183940796451384666445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256245254395268512888593 1692183940796451384666445)
                ·
                  refine ⟨634568977798669269249917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1692183940796451384666445 634568977798669269249917)
                  ·
                    refine ⟨237963366674500975968719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634568977798669269249917 237963366674500975968719)
                    ·
                      rfl

theorem cell22_695148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_695148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695148 prefixEnd_695148 := by exact prefixLift 695148
  have htrace : WordTrace (prefixWord ++ tailWord_695148) baseStart_695148 baseEnd_695148 := by
    simpa [prefixWord, tailWord_695148, baseEnd_695148] using wordTrace_append hprefix tailTrace_695148
  have hstable : (prefixWord ++ tailWord_695148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695148).length < 2 ^ (prefixWord ++ tailWord_695148).sum := by decide
  have hdescent : baseEnd_695148 < baseStart_695148 := by decide
  rcases family_descends (prefixWord ++ tailWord_695148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695150 : List Nat := [4, 1, 2, 3, 2, 1, 3, 6]
def baseStart_695150 : Nat := 118140960795 + 695150 * 2 ^ 59
def prefixEnd_695150 : Nat := 4983230072969 + 3 ^ 40 * 695150 * 2
def baseEnd_695150 : Nat := 26440450146152626379857

theorem tailTrace_695150 : CollatzResearch.WordTrace tailWord_695150 prefixEnd_695150 26440450146152626379857 := by
  unfold tailWord_695150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169275428949718376644363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16902802287731831342103269 3169275428949718376644363)
  ·
    refine ⟨4753913143424577564966545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3169275428949718376644363 4753913143424577564966545)
    ·
      refine ⟨3565434857568433173724909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4753913143424577564966545 3565434857568433173724909)
      ·
        refine ⟨1337038071588162440146841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3565434857568433173724909 1337038071588162440146841)
        ·
          refine ⟨1002778553691121830110131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337038071588162440146841 1002778553691121830110131)
          ·
            refine ⟨1504167830536682745165197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002778553691121830110131 1504167830536682745165197)
            ·
              refine ⟨564062936451256029436949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504167830536682745165197 564062936451256029436949)
              ·
                refine ⟨26440450146152626379857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564062936451256029436949 26440450146152626379857)
                ·
                  rfl

theorem cell22_695150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_695150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695150 prefixEnd_695150 := by exact prefixLift 695150
  have htrace : WordTrace (prefixWord ++ tailWord_695150) baseStart_695150 baseEnd_695150 := by
    simpa [prefixWord, tailWord_695150, baseEnd_695150] using wordTrace_append hprefix tailTrace_695150
  have hstable : (prefixWord ++ tailWord_695150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695150).length < 2 ^ (prefixWord ++ tailWord_695150).sum := by decide
  have hdescent : baseEnd_695150 < baseStart_695150 := by decide
  rcases family_descends (prefixWord ++ tailWord_695150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695165 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_695165 : Nat := 118140960795 + 695165 * 2 ^ 59
def prefixEnd_695165 : Nat := 4983230072969 + 3 ^ 40 * 695165 * 2
def baseEnd_695165 : Nat := 237969186121918598293667

theorem tailTrace_695165 : CollatzResearch.WordTrace tailWord_695165 prefixEnd_695165 237969186121918598293667 := by
  unfold tailWord_695165
  simp only [CollatzResearch.WordTrace]
  refine ⟨25354750526543404574950949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16903167017695603049967299 25354750526543404574950949)
  ·
    refine ⟨4754015723726888357803303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25354750526543404574950949 4754015723726888357803303)
    ·
      refine ⟨7131023585590332536704955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4754015723726888357803303 7131023585590332536704955)
      ·
        refine ⟨10696535378385498805057433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131023585590332536704955 10696535378385498805057433)
        ·
          refine ⟨8022401533789124103793075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10696535378385498805057433 8022401533789124103793075)
          ·
            refine ⟨12033602300683686155689613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8022401533789124103793075 12033602300683686155689613)
            ·
              refine ⟨4512600862756382308383605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12033602300683686155689613 4512600862756382308383605)
              ·
                refine ⟨423056330883410841410963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4512600862756382308383605 423056330883410841410963)
                ·
                  refine ⟨634584496325116262116445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423056330883410841410963 634584496325116262116445)
                  ·
                    refine ⟨237969186121918598293667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634584496325116262116445 237969186121918598293667)
                    ·
                      rfl

theorem cell22_695165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_695165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695165 prefixEnd_695165 := by exact prefixLift 695165
  have htrace : WordTrace (prefixWord ++ tailWord_695165) baseStart_695165 baseEnd_695165 := by
    simpa [prefixWord, tailWord_695165, baseEnd_695165] using wordTrace_append hprefix tailTrace_695165
  have hstable : (prefixWord ++ tailWord_695165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695165).length < 2 ^ (prefixWord ++ tailWord_695165).sum := by decide
  have hdescent : baseEnd_695165 < baseStart_695165 := by decide
  rcases family_descends (prefixWord ++ tailWord_695165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695178 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_695178 : Nat := 118140960795 + 695178 * 2 ^ 59
def prefixEnd_695178 : Nat := 4983230072969 + 3 ^ 40 * 695178 * 2
def baseEnd_695178 : Nat := 79324545429196965906209

theorem tailTrace_695178 : CollatzResearch.WordTrace tailWord_695178 prefixEnd_695178 79324545429196965906209 := by
  unfold tailWord_695178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338806168874076948793547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16903483116997538530116125 6338806168874076948793547)
  ·
    refine ⟨9508209253311115423190321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6338806168874076948793547 9508209253311115423190321)
    ·
      refine ⟨7131156939983336567392741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9508209253311115423190321 7131156939983336567392741)
      ·
        refine ⟨1337091926246875606386139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7131156939983336567392741 1337091926246875606386139)
        ·
          refine ⟨2005637889370313409579209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337091926246875606386139 2005637889370313409579209)
          ·
            refine ⟨1504228417027735057184407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005637889370313409579209 1504228417027735057184407)
            ·
              refine ⟨2256342625541602585776611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504228417027735057184407 2256342625541602585776611)
              ·
                refine ⟨3384513938312403878664917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256342625541602585776611 3384513938312403878664917)
                ·
                  refine ⟨79324545429196965906209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3384513938312403878664917 79324545429196965906209)
                  ·
                    rfl

theorem cell22_695178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_695178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695178 prefixEnd_695178 := by exact prefixLift 695178
  have htrace : WordTrace (prefixWord ++ tailWord_695178) baseStart_695178 baseEnd_695178 := by
    simpa [prefixWord, tailWord_695178, baseEnd_695178] using wordTrace_append hprefix tailTrace_695178
  have hstable : (prefixWord ++ tailWord_695178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695178).length < 2 ^ (prefixWord ++ tailWord_695178).sum := by decide
  have hdescent : baseEnd_695178 < baseStart_695178 := by decide
  rcases family_descends (prefixWord ++ tailWord_695178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695240 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 6]
def baseStart_695240 : Nat := 118140960795 + 695240 * 2 ^ 59
def prefixEnd_695240 : Nat := 4983230072969 + 3 ^ 40 * 695240 * 2
def baseEnd_695240 : Nat := 79331620051547800889479

theorem tailTrace_695240 : CollatzResearch.WordTrace tailWord_695240 prefixEnd_695240 79331620051547800889479 := by
  unfold tailWord_695240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678743000635846191965587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16904990667514461589287449 12678743000635846191965587)
  ·
    refine ⟨19018114500953769287948381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12678743000635846191965587 19018114500953769287948381)
    ·
      refine ⟨7131792937857663482980643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19018114500953769287948381 7131792937857663482980643)
      ·
        refine ⟨10697689406786495224470965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131792937857663482980643 10697689406786495224470965)
        ·
          refine ⟨1002908381886233927294153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10697689406786495224470965 1002908381886233927294153)
          ·
            refine ⟨752181286414675445470615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002908381886233927294153 752181286414675445470615)
            ·
              refine ⟨1128271929622013168205923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752181286414675445470615 1128271929622013168205923)
              ·
                refine ⟨1692407894433019752308885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128271929622013168205923 1692407894433019752308885)
                ·
                  refine ⟨79331620051547800889479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1692407894433019752308885 79331620051547800889479)
                  ·
                    rfl

theorem cell22_695240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_695240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695240 prefixEnd_695240 := by exact prefixLift 695240
  have htrace : WordTrace (prefixWord ++ tailWord_695240) baseStart_695240 baseEnd_695240 := by
    simpa [prefixWord, tailWord_695240, baseEnd_695240] using wordTrace_append hprefix tailTrace_695240
  have hstable : (prefixWord ++ tailWord_695240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695240).length < 2 ^ (prefixWord ++ tailWord_695240).sum := by decide
  have hdescent : baseEnd_695240 < baseStart_695240 := by decide
  rcases family_descends (prefixWord ++ tailWord_695240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695285 : List Nat := [1, 3, 5, 2, 1, 10]
def baseStart_695285 : Nat := 118140960795 + 695285 * 2 ^ 59
def prefixEnd_695285 : Nat := 4983230072969 + 3 ^ 40 * 695285 * 2
def baseEnd_695285 : Nat := 2938398328077509694979

theorem tailTrace_695285 : CollatzResearch.WordTrace tailWord_695285 prefixEnd_695285 2938398328077509694979 := by
  unfold tailWord_695285
  simp only [CollatzResearch.WordTrace]
  refine ⟨25359127286108665069319309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16906084857405776712879539 25359127286108665069319309)
  ·
    refine ⟨9509672732290749400994741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25359127286108665069319309 9509672732290749400994741)
    ·
      refine ⟨891531818652257756343257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9509672732290749400994741 891531818652257756343257)
      ·
        refine ⟨668648863989193317257443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891531818652257756343257 668648863989193317257443)
        ·
          refine ⟨1002973295983789975886165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668648863989193317257443 1002973295983789975886165)
          ·
            refine ⟨2938398328077509694979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1002973295983789975886165 2938398328077509694979)
            ·
              rfl

theorem cell22_695285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 10].length) (baseStart_695285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695285 prefixEnd_695285 := by exact prefixLift 695285
  have htrace : WordTrace (prefixWord ++ tailWord_695285) baseStart_695285 baseEnd_695285 := by
    simpa [prefixWord, tailWord_695285, baseEnd_695285] using wordTrace_append hprefix tailTrace_695285
  have hstable : (prefixWord ++ tailWord_695285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695285).length < 2 ^ (prefixWord ++ tailWord_695285).sum := by decide
  have hdescent : baseEnd_695285 < baseStart_695285 := by decide
  rcases family_descends (prefixWord ++ tailWord_695285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695296 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_695296 : Nat := 118140960795 + 695296 * 2 ^ 59
def prefixEnd_695296 : Nat := 4983230072969 + 3 ^ 40 * 695296 * 2
def baseEnd_695296 : Nat := 79338010033025974422755

theorem tailTrace_695296 : CollatzResearch.WordTrace tailWord_695296 prefixEnd_695296 79338010033025974422755 := by
  unfold tailWord_695296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679764244534406973984871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16906352326045875965313161 12679764244534406973984871)
  ·
    refine ⟨19019646366801610460977307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12679764244534406973984871 19019646366801610460977307)
    ·
      refine ⟨28529469550202415691465961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19019646366801610460977307 28529469550202415691465961)
      ·
        refine ⟨21397102162651811768599471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28529469550202415691465961 21397102162651811768599471)
        ·
          refine ⟨32095653243977717652899207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21397102162651811768599471 32095653243977717652899207)
          ·
            refine ⟨48143479865966576479348811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32095653243977717652899207 48143479865966576479348811)
            ·
              refine ⟨72215219798949864719023217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48143479865966576479348811 72215219798949864719023217)
              ·
                refine ⟨54161414849212398539267413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72215219798949864719023217 54161414849212398539267413)
                ·
                  refine ⟨79338010033025974422755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 54161414849212398539267413 79338010033025974422755)
                  ·
                    rfl

theorem cell22_695296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_695296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695296 prefixEnd_695296 := by exact prefixLift 695296
  have htrace : WordTrace (prefixWord ++ tailWord_695296) baseStart_695296 baseEnd_695296 := by
    simpa [prefixWord, tailWord_695296, baseEnd_695296] using wordTrace_append hprefix tailTrace_695296
  have hstable : (prefixWord ++ tailWord_695296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695296).length < 2 ^ (prefixWord ++ tailWord_695296).sum := by decide
  have hdescent : baseEnd_695296 < baseStart_695296 := by decide
  rcases family_descends (prefixWord ++ tailWord_695296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695405 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_695405 : Nat := 118140960795 + 695405 * 2 ^ 59
def prefixEnd_695405 : Nat := 4983230072969 + 3 ^ 40 * 695405 * 2
def baseEnd_695405 : Nat := 238051343026637972292931

theorem tailTrace_695405 : CollatzResearch.WordTrace tailWord_695405 prefixEnd_695405 238051343026637972292931 := by
  unfold tailWord_695405
  simp only [CollatzResearch.WordTrace]
  refine ⟨25363504045673925563687669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16909002697115950375791779 25363504045673925563687669)
  ·
    refine ⟨2377828504281930521595719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25363504045673925563687669 2377828504281930521595719)
    ·
      refine ⟨3566742756422895782393579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2377828504281930521595719 3566742756422895782393579)
      ·
        refine ⟨5350114134634343673590369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566742756422895782393579 5350114134634343673590369)
        ·
          refine ⟨4012585600975757755192777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5350114134634343673590369 4012585600975757755192777)
          ·
            refine ⟨3009439200731818316394583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012585600975757755192777 3009439200731818316394583)
            ·
              refine ⟨4514158801097727474591875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009439200731818316394583 4514158801097727474591875)
              ·
                refine ⟨6771238201646591211887813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514158801097727474591875 6771238201646591211887813)
                ·
                  refine ⟨1269607162808735852228965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6771238201646591211887813 1269607162808735852228965)
                  ·
                    refine ⟨238051343026637972292931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1269607162808735852228965 238051343026637972292931)
                    ·
                      rfl

theorem cell22_695405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_695405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695405 prefixEnd_695405 := by exact prefixLift 695405
  have htrace : WordTrace (prefixWord ++ tailWord_695405) baseStart_695405 baseEnd_695405 := by
    simpa [prefixWord, tailWord_695405, baseEnd_695405] using wordTrace_append hprefix tailTrace_695405
  have hstable : (prefixWord ++ tailWord_695405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695405).length < 2 ^ (prefixWord ++ tailWord_695405).sum := by decide
  have hdescent : baseEnd_695405 < baseStart_695405 := by decide
  rcases family_descends (prefixWord ++ tailWord_695405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695435 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 3, 3]
def baseStart_695435 : Nat := 118140960795 + 695435 * 2 ^ 59
def prefixEnd_695435 : Nat := 4983230072969 + 3 ^ 40 * 695435 * 2
def baseEnd_695435 : Nat := 238061612639727894042839

theorem tailTrace_695435 : CollatzResearch.WordTrace tailWord_695435 prefixEnd_695435 238061612639727894042839 := by
  unfold tailWord_695435
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364598235565240687279759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16909732157043493791519839 25364598235565240687279759)
  ·
    refine ⟨38046897353347861030919639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25364598235565240687279759 38046897353347861030919639)
    ·
      refine ⟨57070346030021791546379459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38046897353347861030919639 57070346030021791546379459)
      ·
        refine ⟨85605519045032687319569189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57070346030021791546379459 85605519045032687319569189)
        ·
          refine ⟨16051034820943628872419223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85605519045032687319569189 16051034820943628872419223)
          ·
            refine ⟨24076552231415443308628835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16051034820943628872419223 24076552231415443308628835)
            ·
              refine ⟨36114828347123164962943253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24076552231415443308628835 36114828347123164962943253)
              ·
                refine ⟨1692882578771398357637965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36114828347123164962943253 1692882578771398357637965)
                ·
                  refine ⟨634830967039274384114237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1692882578771398357637965 634830967039274384114237)
                  ·
                    refine ⟨238061612639727894042839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634830967039274384114237 238061612639727894042839)
                    ·
                      rfl

theorem cell22_695435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 3].length) (baseStart_695435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695435 prefixEnd_695435 := by exact prefixLift 695435
  have htrace : WordTrace (prefixWord ++ tailWord_695435) baseStart_695435 baseEnd_695435 := by
    simpa [prefixWord, tailWord_695435, baseEnd_695435] using wordTrace_append hprefix tailTrace_695435
  have hstable : (prefixWord ++ tailWord_695435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695435).length < 2 ^ (prefixWord ++ tailWord_695435).sum := by decide
  have hdescent : baseEnd_695435 < baseStart_695435 := by decide
  rcases family_descends (prefixWord ++ tailWord_695435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695555 : List Nat := [1, 1, 1, 3, 2, 5, 1, 8]
def baseStart_695555 : Nat := 118140960795 + 695555 * 2 ^ 59
def prefixEnd_695555 : Nat := 4983230072969 + 3 ^ 40 * 695555 * 2
def baseEnd_695555 : Nat := 26455854565787509004719

theorem tailTrace_695555 : CollatzResearch.WordTrace tailWord_695555 prefixEnd_695555 26455854565787509004719 := by
  unfold tailWord_695555
  simp only [CollatzResearch.WordTrace]
  refine ⟨25368974995130501181648119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16912649996753667454432079 25368974995130501181648119)
  ·
    refine ⟨38053462492695751772472179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25368974995130501181648119 38053462492695751772472179)
    ·
      refine ⟨57080193739043627658708269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38053462492695751772472179 57080193739043627658708269)
      ·
        refine ⟨21405072652141360372015601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57080193739043627658708269 21405072652141360372015601)
        ·
          refine ⟨16053804489106020279011701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21405072652141360372015601 16053804489106020279011701)
          ·
            refine ⟨1505044170853689401157347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16053804489106020279011701 1505044170853689401157347)
            ·
              refine ⟨2257566256280534101736021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505044170853689401157347 2257566256280534101736021)
              ·
                refine ⟨26455854565787509004719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2257566256280534101736021 26455854565787509004719)
                ·
                  rfl

theorem cell22_695555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 8].length) (baseStart_695555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695555 prefixEnd_695555 := by exact prefixLift 695555
  have htrace : WordTrace (prefixWord ++ tailWord_695555) baseStart_695555 baseEnd_695555 := by
    simpa [prefixWord, tailWord_695555, baseEnd_695555] using wordTrace_append hprefix tailTrace_695555
  have hstable : (prefixWord ++ tailWord_695555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695555).length < 2 ^ (prefixWord ++ tailWord_695555).sum := by decide
  have hdescent : baseEnd_695555 < baseStart_695555 := by decide
  rcases family_descends (prefixWord ++ tailWord_695555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695585 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_695585 : Nat := 118140960795 + 695585 * 2 ^ 59
def prefixEnd_695585 : Nat := 4983230072969 + 3 ^ 40 * 695585 * 2
def baseEnd_695585 : Nat := 238112960705177502792379

theorem tailTrace_695585 : CollatzResearch.WordTrace tailWord_695585 prefixEnd_695585 238112960705177502792379 := by
  unfold tailWord_695585
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370069185021816305240209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16913379456681210870160139 25370069185021816305240209)
  ·
    refine ⟨19027551888766362228930157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25370069185021816305240209 19027551888766362228930157)
    ·
      refine ⟨7135331958287385835848809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19027551888766362228930157 7135331958287385835848809)
      ·
        refine ⟨5351498968715539376886607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7135331958287385835848809 5351498968715539376886607)
        ·
          refine ⟨8027248453073309065329911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351498968715539376886607 8027248453073309065329911)
          ·
            refine ⟨12040872679609963597994867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027248453073309065329911 12040872679609963597994867)
            ·
              refine ⟨18061309019414945396992301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12040872679609963597994867 18061309019414945396992301)
              ·
                refine ⟨6772990882280604523872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18061309019414945396992301 6772990882280604523872113)
                ·
                  refine ⟨5079743161710453392904085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6772990882280604523872113 5079743161710453392904085)
                  ·
                    refine ⟨238112960705177502792379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5079743161710453392904085 238112960705177502792379)
                    ·
                      rfl

theorem cell22_695585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_695585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695585 prefixEnd_695585 := by exact prefixLift 695585
  have htrace : WordTrace (prefixWord ++ tailWord_695585) baseStart_695585 baseEnd_695585 := by
    simpa [prefixWord, tailWord_695585, baseEnd_695585] using wordTrace_append hprefix tailTrace_695585
  have hstable : (prefixWord ++ tailWord_695585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695585).length < 2 ^ (prefixWord ++ tailWord_695585).sum := by decide
  have hdescent : baseEnd_695585 < baseStart_695585 := by decide
  rcases family_descends (prefixWord ++ tailWord_695585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695604 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_695604 : Nat := 118140960795 + 695604 * 2 ^ 59
def prefixEnd_695604 : Nat := 4983230072969 + 3 ^ 40 * 695604 * 2
def baseEnd_695604 : Nat := 238119464793467786567321

theorem tailTrace_695604 : CollatzResearch.WordTrace tailWord_695604 prefixEnd_695604 238119464793467786567321 := by
  unfold tailWord_695604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12685381085976491275090933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16913841447968655033454577 12685381085976491275090933)
  ·
    refine ⟨1189254476810296057039775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12685381085976491275090933 1189254476810296057039775)
    ·
      refine ⟨1783881715215444085559663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189254476810296057039775 1783881715215444085559663)
      ·
        refine ⟨2675822572823166128339495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783881715215444085559663 2675822572823166128339495)
        ·
          refine ⟨4013733859234749192509243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675822572823166128339495 4013733859234749192509243)
          ·
            refine ⟨6020600788852123788763865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013733859234749192509243 6020600788852123788763865)
            ·
              refine ⟨4515450591639092841572899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6020600788852123788763865 4515450591639092841572899)
              ·
                refine ⟨6773175887458639262359349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4515450591639092841572899 6773175887458639262359349)
                ·
                  refine ⟨634985239449247430846189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6773175887458639262359349 634985239449247430846189)
                  ·
                    refine ⟨238119464793467786567321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634985239449247430846189 238119464793467786567321)
                    ·
                      rfl

theorem cell22_695604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_695604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695604 prefixEnd_695604 := by exact prefixLift 695604
  have htrace : WordTrace (prefixWord ++ tailWord_695604) baseStart_695604 baseEnd_695604 := by
    simpa [prefixWord, tailWord_695604, baseEnd_695604] using wordTrace_append hprefix tailTrace_695604
  have hstable : (prefixWord ++ tailWord_695604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695604).length < 2 ^ (prefixWord ++ tailWord_695604).sum := by decide
  have hdescent : baseEnd_695604 < baseStart_695604 := by decide
  rcases family_descends (prefixWord ++ tailWord_695604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695677 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_695677 : Nat := 118140960795 + 695677 * 2 ^ 59
def prefixEnd_695677 : Nat := 4983230072969 + 3 ^ 40 * 695677 * 2
def baseEnd_695677 : Nat := 238144454185319929492097

theorem tailTrace_695677 : CollatzResearch.WordTrace tailWord_695677 prefixEnd_695677 238144454185319929492097 := by
  unfold tailWord_695677
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373424700688516017589285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16915616467125677345059523 25373424700688516017589285)
  ·
    refine ⟨4757517131379096753297991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25373424700688516017589285 4757517131379096753297991)
    ·
      refine ⟨7136275697068645129946987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757517131379096753297991 7136275697068645129946987)
      ·
        refine ⟨10704413545602967694920481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136275697068645129946987 10704413545602967694920481)
        ·
          refine ⟨8028310159202225771190361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10704413545602967694920481 8028310159202225771190361)
          ·
            refine ⟨6021232619401669328392771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8028310159202225771190361 6021232619401669328392771)
            ·
              refine ⟨9031848929102503992589157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021232619401669328392771 9031848929102503992589157)
              ·
                refine ⟨1693471674206719498610467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9031848929102503992589157 1693471674206719498610467)
                ·
                  refine ⟨2540207511310079247915701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693471674206719498610467 2540207511310079247915701)
                  ·
                    refine ⟨238144454185319929492097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2540207511310079247915701 238144454185319929492097)
                    ·
                      rfl

theorem cell22_695677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_695677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695677 prefixEnd_695677 := by exact prefixLift 695677
  have htrace : WordTrace (prefixWord ++ tailWord_695677) baseStart_695677 baseEnd_695677 := by
    simpa [prefixWord, tailWord_695677, baseEnd_695677] using wordTrace_append hprefix tailTrace_695677
  have hstable : (prefixWord ++ tailWord_695677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695677).length < 2 ^ (prefixWord ++ tailWord_695677).sum := by decide
  have hdescent : baseEnd_695677 < baseStart_695677 := by decide
  rcases family_descends (prefixWord ++ tailWord_695677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695681 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_695681 : Nat := 118140960795 + 695681 * 2 ^ 59
def prefixEnd_695681 : Nat := 4983230072969 + 3 ^ 40 * 695681 * 2
def baseEnd_695681 : Nat := 238145823467065252392085

theorem tailTrace_695681 : CollatzResearch.WordTrace tailWord_695681 prefixEnd_695681 238145823467065252392085 := by
  unfold tailWord_695681
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373570592674024700734897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16915713728449349800489931 25373570592674024700734897)
  ·
    refine ⟨19030177944505518525551173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25373570592674024700734897 19030177944505518525551173)
    ·
      refine ⟨3568158364594784723540845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19030177944505518525551173 3568158364594784723540845)
      ·
        refine ⟨1338059386723044271327817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3568158364594784723540845 1338059386723044271327817)
        ·
          refine ⟨1003544540042283203495863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338059386723044271327817 1003544540042283203495863)
          ·
            refine ⟨1505316810063424805243795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003544540042283203495863 1505316810063424805243795)
            ·
              refine ⟨2257975215095137207865693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505316810063424805243795 2257975215095137207865693)
              ·
                refine ⟨846740705660676452949635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257975215095137207865693 846740705660676452949635)
                ·
                  refine ⟨1270111058491014679424453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846740705660676452949635 1270111058491014679424453)
                  ·
                    refine ⟨238145823467065252392085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270111058491014679424453 238145823467065252392085)
                    ·
                      rfl

theorem cell22_695681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_695681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695681 prefixEnd_695681 := by exact prefixLift 695681
  have htrace : WordTrace (prefixWord ++ tailWord_695681) baseStart_695681 baseEnd_695681 := by
    simpa [prefixWord, tailWord_695681, baseEnd_695681] using wordTrace_append hprefix tailTrace_695681
  have hstable : (prefixWord ++ tailWord_695681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695681).length < 2 ^ (prefixWord ++ tailWord_695681).sum := by decide
  have hdescent : baseEnd_695681 < baseStart_695681 := by decide
  rcases family_descends (prefixWord ++ tailWord_695681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695692 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_695692 : Nat := 118140960795 + 695692 * 2 ^ 59
def prefixEnd_695692 : Nat := 4983230072969 + 3 ^ 40 * 695692 * 2
def baseEnd_695692 : Nat := 238149588991864890367051

theorem tailTrace_695692 : CollatzResearch.WordTrace tailWord_695692 prefixEnd_695692 238149588991864890367051 := by
  unfold tailWord_695692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686985897817086789692665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16915981197089449052923553 12686985897817086789692665)
  ·
    refine ⟨9515239423362815092269499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12686985897817086789692665 9515239423362815092269499)
    ·
      refine ⟨14272859135044222638404249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515239423362815092269499 14272859135044222638404249)
      ·
        refine ⟨10704644351283166978803187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14272859135044222638404249 10704644351283166978803187)
        ·
          refine ⟨16056966526924750468204781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10704644351283166978803187 16056966526924750468204781)
          ·
            refine ⟨6021362447596781425576793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16056966526924750468204781 6021362447596781425576793)
            ·
              refine ⟨4516021835697586069182595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6021362447596781425576793 4516021835697586069182595)
              ·
                refine ⟨6774032753546379103773893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4516021835697586069182595 6774032753546379103773893)
                ·
                  refine ⟨1270131141289946081957605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6774032753546379103773893 1270131141289946081957605)
                  ·
                    refine ⟨238149588991864890367051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270131141289946081957605 238149588991864890367051)
                    ·
                      rfl

theorem cell22_695692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_695692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695692 prefixEnd_695692 := by exact prefixLift 695692
  have htrace : WordTrace (prefixWord ++ tailWord_695692) baseStart_695692 baseEnd_695692 := by
    simpa [prefixWord, tailWord_695692, baseEnd_695692] using wordTrace_append hprefix tailTrace_695692
  have hstable : (prefixWord ++ tailWord_695692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695692).length < 2 ^ (prefixWord ++ tailWord_695692).sum := by decide
  have hdescent : baseEnd_695692 < baseStart_695692 := by decide
  rcases family_descends (prefixWord ++ tailWord_695692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695752 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_695752 : Nat := 118140960795 + 695752 * 2 ^ 59
def prefixEnd_695752 : Nat := 4983230072969 + 3 ^ 40 * 695752 * 2
def baseEnd_695752 : Nat := 79390042739348244622289

theorem tailTrace_695752 : CollatzResearch.WordTrace tailWord_695752 prefixEnd_695752 79390042739348244622289 := by
  unfold tailWord_695752
  simp only [CollatzResearch.WordTrace]
  refine ⟨12688080087708401913284755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16917440116944535884379673 12688080087708401913284755)
  ·
    refine ⟨19032120131562602869927133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12688080087708401913284755 19032120131562602869927133)
    ·
      refine ⟨7137045049335976076222675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19032120131562602869927133 7137045049335976076222675)
      ·
        refine ⟨10705567574003964114334013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7137045049335976076222675 10705567574003964114334013)
        ·
          refine ⟨4014587840251486542875255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10705567574003964114334013 4014587840251486542875255)
          ·
            refine ⟨6021881760377229814312883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014587840251486542875255 6021881760377229814312883)
            ·
              refine ⟨9032822640565844721469325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021881760377229814312883 9032822640565844721469325)
              ·
                refine ⟨3387308490212191770550997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9032822640565844721469325 3387308490212191770550997)
                ·
                  refine ⟨79390042739348244622289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3387308490212191770550997 79390042739348244622289)
                  ·
                    rfl

theorem cell22_695752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_695752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695752 prefixEnd_695752 := by exact prefixLift 695752
  have htrace : WordTrace (prefixWord ++ tailWord_695752) baseStart_695752 baseEnd_695752 := by
    simpa [prefixWord, tailWord_695752, baseEnd_695752] using wordTrace_append hprefix tailTrace_695752
  have hstable : (prefixWord ++ tailWord_695752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695752).length < 2 ^ (prefixWord ++ tailWord_695752).sum := by decide
  have hdescent : baseEnd_695752 < baseStart_695752 := by decide
  rcases family_descends (prefixWord ++ tailWord_695752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695756 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_695756 : Nat := 118140960795 + 695756 * 2 ^ 59
def prefixEnd_695756 : Nat := 4983230072969 + 3 ^ 40 * 695756 * 2
def baseEnd_695756 : Nat := 238171497499790056766855

theorem tailTrace_695756 : CollatzResearch.WordTrace tailWord_695756 prefixEnd_695756 238171497499790056766855 := by
  unfold tailWord_695756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12688153033701156254857561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16917537378268208339810081 12688153033701156254857561)
  ·
    refine ⟨9516114775275867191143171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12688153033701156254857561 9516114775275867191143171)
    ·
      refine ⟨14274172162913800786714757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9516114775275867191143171 14274172162913800786714757)
      ·
        refine ⟨2676407280546337647509017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14274172162913800786714757 2676407280546337647509017)
        ·
          refine ⟨2007305460409753235631763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676407280546337647509017 2007305460409753235631763)
          ·
            refine ⟨3010958190614629853447645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007305460409753235631763 3010958190614629853447645)
            ·
              refine ⟨1129109321480486195042867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3010958190614629853447645 1129109321480486195042867)
              ·
                refine ⟨1693663982220729292564301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129109321480486195042867 1693663982220729292564301)
                ·
                  refine ⟨635123993332773484711613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1693663982220729292564301 635123993332773484711613)
                  ·
                    refine ⟨238171497499790056766855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635123993332773484711613 238171497499790056766855)
                    ·
                      rfl

theorem cell22_695756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_695756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695756 prefixEnd_695756 := by exact prefixLift 695756
  have htrace : WordTrace (prefixWord ++ tailWord_695756) baseStart_695756 baseEnd_695756 := by
    simpa [prefixWord, tailWord_695756, baseEnd_695756] using wordTrace_append hprefix tailTrace_695756
  have hstable : (prefixWord ++ tailWord_695756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695756).length < 2 ^ (prefixWord ++ tailWord_695756).sum := by decide
  have hdescent : baseEnd_695756 < baseStart_695756 := by decide
  rcases family_descends (prefixWord ++ tailWord_695756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695767 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_695767 : Nat := 118140960795 + 695767 * 2 ^ 59
def prefixEnd_695767 : Nat := 4983230072969 + 3 ^ 40 * 695767 * 2
def baseEnd_695767 : Nat := 238175263024589694741821

theorem tailTrace_695767 : CollatzResearch.WordTrace tailWord_695767 prefixEnd_695767 238175263024589694741821 := by
  unfold tailWord_695767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25376707270362461388365555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16917804846908307592243703 25376707270362461388365555)
  ·
    refine ⟨38065060905543692082548333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25376707270362461388365555 38065060905543692082548333)
    ·
      refine ⟨14274397839578884530955625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38065060905543692082548333 14274397839578884530955625)
      ·
        refine ⟨10705798379684163398216719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14274397839578884530955625 10705798379684163398216719)
        ·
          refine ⟨16058697569526245097325079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705798379684163398216719 16058697569526245097325079)
          ·
            refine ⟨24088046354289367645987619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16058697569526245097325079 24088046354289367645987619)
            ·
              refine ⟨36132069531434051468981429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24088046354289367645987619 36132069531434051468981429)
              ·
                refine ⟨3387381518571942325217009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36132069531434051468981429 3387381518571942325217009)
                ·
                  refine ⟨2540536138928956743912757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387381518571942325217009 2540536138928956743912757)
                  ·
                    refine ⟨238175263024589694741821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2540536138928956743912757 238175263024589694741821)
                    ·
                      rfl

theorem cell22_695767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_695767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695767 prefixEnd_695767 := by exact prefixLift 695767
  have htrace : WordTrace (prefixWord ++ tailWord_695767) baseStart_695767 baseEnd_695767 := by
    simpa [prefixWord, tailWord_695767, baseEnd_695767] using wordTrace_append hprefix tailTrace_695767
  have hstable : (prefixWord ++ tailWord_695767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695767).length < 2 ^ (prefixWord ++ tailWord_695767).sum := by decide
  have hdescent : baseEnd_695767 < baseStart_695767 := by decide
  rcases family_descends (prefixWord ++ tailWord_695767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695769 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 5]
def baseStart_695769 : Nat := 118140960795 + 695769 * 2 ^ 59
def prefixEnd_695769 : Nat := 4983230072969 + 3 ^ 40 * 695769 * 2
def baseEnd_695769 : Nat := 79391982555154118730605

theorem tailTrace_695769 : CollatzResearch.WordTrace tailWord_695769 prefixEnd_695769 79391982555154118730605 := by
  unfold tailWord_695769
  simp only [CollatzResearch.WordTrace]
  refine ⟨25376780216355215729938361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16917853477570143819958907 25376780216355215729938361)
  ·
    refine ⟨19032585162266411797453771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25376780216355215729938361 19032585162266411797453771)
    ·
      refine ⟨28548877743399617696180657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19032585162266411797453771 28548877743399617696180657)
      ·
        refine ⟨21411658307549713272135493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28548877743399617696180657 21411658307549713272135493)
        ·
          refine ⟨4014685932665571238525405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21411658307549713272135493 4014685932665571238525405)
          ·
            refine ⟨1505507224749589214447027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4014685932665571238525405 1505507224749589214447027)
            ·
              refine ⟨2258260837124383821670541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505507224749589214447027 2258260837124383821670541)
              ·
                refine ⟨846847813921643933126453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2258260837124383821670541 846847813921643933126453)
                ·
                  refine ⟨79391982555154118730605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846847813921643933126453 79391982555154118730605)
                  ·
                    rfl

theorem cell22_695769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_695769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695769 prefixEnd_695769 := by exact prefixLift 695769
  have htrace : WordTrace (prefixWord ++ tailWord_695769) baseStart_695769 baseEnd_695769 := by
    simpa [prefixWord, tailWord_695769, baseEnd_695769] using wordTrace_append hprefix tailTrace_695769
  have hstable : (prefixWord ++ tailWord_695769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695769).length < 2 ^ (prefixWord ++ tailWord_695769).sum := by decide
  have hdescent : baseEnd_695769 < baseStart_695769 := by decide
  rcases family_descends (prefixWord ++ tailWord_695769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695829 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_695829 : Nat := 118140960795 + 695829 * 2 ^ 59
def prefixEnd_695829 : Nat := 4983230072969 + 3 ^ 40 * 695829 * 2
def baseEnd_695829 : Nat := 238196486891642199691631

theorem tailTrace_695829 : CollatzResearch.WordTrace tailWord_695829 prefixEnd_695829 238196486891642199691631 := by
  unfold tailWord_695829
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378968596137845977122541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16919312397425230651415027 25378968596137845977122541)
  ·
    refine ⟨9517113223551692241420953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25378968596137845977122541 9517113223551692241420953)
    ·
      refine ⟨7137834917663769181065715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9517113223551692241420953 7137834917663769181065715)
      ·
        refine ⟨10706752376495653771598573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7137834917663769181065715 10706752376495653771598573)
        ·
          refine ⟨4015032141185870164349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10706752376495653771598573 4015032141185870164349465)
          ·
            refine ⟨3011274105889402623262099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4015032141185870164349465 3011274105889402623262099)
            ·
              refine ⟨4516911158834103934893149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011274105889402623262099 4516911158834103934893149)
              ·
                refine ⟨1693841684562788975584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4516911158834103934893149 1693841684562788975584931)
                ·
                  refine ⟨2540762526844183463377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693841684562788975584931 2540762526844183463377397)
                  ·
                    refine ⟨238196486891642199691631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2540762526844183463377397 238196486891642199691631)
                    ·
                      rfl

theorem cell22_695829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_695829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695829 prefixEnd_695829 := by exact prefixLift 695829
  have htrace : WordTrace (prefixWord ++ tailWord_695829) baseStart_695829 baseEnd_695829 := by
    simpa [prefixWord, tailWord_695829, baseEnd_695829] using wordTrace_append hprefix tailTrace_695829
  have hstable : (prefixWord ++ tailWord_695829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695829).length < 2 ^ (prefixWord ++ tailWord_695829).sum := by decide
  have hdescent : baseEnd_695829 < baseStart_695829 := by decide
  rcases family_descends (prefixWord ++ tailWord_695829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695863 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 2, 3]
def baseStart_695863 : Nat := 118140960795 + 695863 * 2 ^ 59
def prefixEnd_695863 : Nat := 4983230072969 + 3 ^ 40 * 695863 * 2
def baseEnd_695863 : Nat := 238208125786477444341527

theorem tailTrace_695863 : CollatzResearch.WordTrace tailWord_695863 prefixEnd_695863 238208125786477444341527 := by
  unfold tailWord_695863
  simp only [CollatzResearch.WordTrace]
  refine ⟨25380208678014669783860243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16920139118676446522573495 25380208678014669783860243)
  ·
    refine ⟨38070313017022004675790365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25380208678014669783860243 38070313017022004675790365)
    ·
      refine ⟨14276367381383251753421387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38070313017022004675790365 14276367381383251753421387)
      ·
        refine ⟨21414551072074877630132081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14276367381383251753421387 21414551072074877630132081)
        ·
          refine ⟨16060913304056158222599061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21414551072074877630132081 16060913304056158222599061)
          ·
            refine ⟨752855311127632416684331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16060913304056158222599061 752855311127632416684331)
            ·
              refine ⟨1129282966691448625026497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752855311127632416684331 1129282966691448625026497)
              ·
                refine ⟨846962225018586468769873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129282966691448625026497 846962225018586468769873)
                ·
                  refine ⟨635221668763939851577405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846962225018586468769873 635221668763939851577405)
                  ·
                    refine ⟨238208125786477444341527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635221668763939851577405 238208125786477444341527)
                    ·
                      rfl

theorem cell22_695863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_695863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695863 prefixEnd_695863 := by exact prefixLift 695863
  have htrace : WordTrace (prefixWord ++ tailWord_695863) baseStart_695863 baseEnd_695863 := by
    simpa [prefixWord, tailWord_695863, baseEnd_695863] using wordTrace_append hprefix tailTrace_695863
  have hstable : (prefixWord ++ tailWord_695863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695863).length < 2 ^ (prefixWord ++ tailWord_695863).sum := by decide
  have hdescent : baseEnd_695863 < baseStart_695863 := by decide
  rcases family_descends (prefixWord ++ tailWord_695863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695925 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_695925 : Nat := 118140960795 + 695925 * 2 ^ 59
def prefixEnd_695925 : Nat := 4983230072969 + 3 ^ 40 * 695925 * 2
def baseEnd_695925 : Nat := 238229349653529949291337

theorem tailTrace_695925 : CollatzResearch.WordTrace tailWord_695925 prefixEnd_695925 238229349653529949291337 := by
  unfold tailWord_695925
  simp only [CollatzResearch.WordTrace]
  refine ⟨25382470003790054372617229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16921646669193369581744819 25382470003790054372617229)
  ·
    refine ⟨9518426251421270389731461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25382470003790054372617229 9518426251421270389731461)
    ·
      refine ⟨1784704922141488198074649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9518426251421270389731461 1784704922141488198074649)
      ·
        refine ⟨1338528691606116148555987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1784704922141488198074649 1338528691606116148555987)
        ·
          refine ⟨2007793037409174222833981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1338528691606116148555987 2007793037409174222833981)
          ·
            refine ⟨752922389028440333562743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2007793037409174222833981 752922389028440333562743)
            ·
              refine ⟨1129383583542660500344115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752922389028440333562743 1129383583542660500344115)
              ·
                refine ⟨1694075375313990750516173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129383583542660500344115 1694075375313990750516173)
                ·
                  refine ⟨635278265742746531443565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1694075375313990750516173 635278265742746531443565)
                  ·
                    refine ⟨238229349653529949291337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635278265742746531443565 238229349653529949291337)
                    ·
                      rfl

theorem cell22_695925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_695925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695925 prefixEnd_695925 := by exact prefixLift 695925
  have htrace : WordTrace (prefixWord ++ tailWord_695925) baseStart_695925 baseEnd_695925 := by
    simpa [prefixWord, tailWord_695925, baseEnd_695925] using wordTrace_append hprefix tailTrace_695925
  have hstable : (prefixWord ++ tailWord_695925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695925).length < 2 ^ (prefixWord ++ tailWord_695925).sum := by decide
  have hdescent : baseEnd_695925 < baseStart_695925 := by decide
  rcases family_descends (prefixWord ++ tailWord_695925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695981 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_695981 : Nat := 118140960795 + 695981 * 2 ^ 59
def prefixEnd_695981 : Nat := 4983230072969 + 3 ^ 40 * 695981 * 2
def baseEnd_695981 : Nat := 238248519597964469891165

theorem tailTrace_695981 : CollatzResearch.WordTrace tailWord_695981 prefixEnd_695981 238248519597964469891165 := by
  unfold tailWord_695981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25384512491587175936655797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16923008327724783957770531 25384512491587175936655797)
  ·
    refine ⟨2379798046086297744061481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25384512491587175936655797 2379798046086297744061481)
    ·
      refine ⟨1784848534564723308046111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2379798046086297744061481 1784848534564723308046111)
      ·
        refine ⟨2677272801847084962069167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784848534564723308046111 2677272801847084962069167)
        ·
          refine ⟨4015909202770627443103751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677272801847084962069167 4015909202770627443103751)
          ·
            refine ⟨6023863804155941164655627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015909202770627443103751 6023863804155941164655627)
            ·
              refine ⟨9035795706233911746983441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023863804155941164655627 9035795706233911746983441)
              ·
                refine ⟨6776846779675433810237581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035795706233911746983441 6776846779675433810237581)
                ·
                  refine ⟨2541317542378287678839093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6776846779675433810237581 2541317542378287678839093)
                  ·
                    refine ⟨238248519597964469891165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2541317542378287678839093 238248519597964469891165)
                    ·
                      rfl

theorem cell22_695981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_695981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695981 prefixEnd_695981 := by exact prefixLift 695981
  have htrace : WordTrace (prefixWord ++ tailWord_695981) baseStart_695981 baseEnd_695981 := by
    simpa [prefixWord, tailWord_695981, baseEnd_695981] using wordTrace_append hprefix tailTrace_695981
  have hstable : (prefixWord ++ tailWord_695981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695981).length < 2 ^ (prefixWord ++ tailWord_695981).sum := by decide
  have hdescent : baseEnd_695981 < baseStart_695981 := by decide
  rcases family_descends (prefixWord ++ tailWord_695981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695998 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_695998 : Nat := 118140960795 + 695998 * 2 ^ 59
def prefixEnd_695998 : Nat := 4983230072969 + 3 ^ 40 * 695998 * 2
def baseEnd_695998 : Nat := 238254339045382092216113

theorem tailTrace_695998 : CollatzResearch.WordTrace tailWord_695998 prefixEnd_695998 238254339045382092216113 := by
  unfold tailWord_695998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173141566565698480003081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16923421688350391893349765 3173141566565698480003081)
  ·
    refine ⟨2379856174924273860002311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3173141566565698480003081 2379856174924273860002311)
    ·
      refine ⟨3569784262386410790003467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379856174924273860002311 3569784262386410790003467)
      ·
        refine ⟨5354676393579616185005201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3569784262386410790003467 5354676393579616185005201)
        ·
          refine ⟨4016007295184712138753901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5354676393579616185005201 4016007295184712138753901)
          ·
            refine ⟨1506002735694267052032713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4016007295184712138753901 1506002735694267052032713)
            ·
              refine ⟨1129502051770700289024535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506002735694267052032713 1129502051770700289024535)
              ·
                refine ⟨1694253077656050433536803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129502051770700289024535 1694253077656050433536803)
                ·
                  refine ⟨2541379616484075650305205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694253077656050433536803 2541379616484075650305205)
                  ·
                    refine ⟨238254339045382092216113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2541379616484075650305205 238254339045382092216113)
                    ·
                      rfl

theorem cell22_695998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_695998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_695998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_695998 prefixEnd_695998 := by exact prefixLift 695998
  have htrace : WordTrace (prefixWord ++ tailWord_695998) baseStart_695998 baseEnd_695998 := by
    simpa [prefixWord, tailWord_695998, baseEnd_695998] using wordTrace_append hprefix tailTrace_695998
  have hstable : (prefixWord ++ tailWord_695998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695998).length < 2 ^ (prefixWord ++ tailWord_695998).sum := by decide
  have hdescent : baseEnd_695998 < baseStart_695998 := by decide
  rcases family_descends (prefixWord ++ tailWord_695998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696028 : List Nat := [2, 2, 5, 1, 2, 1, 9]
def baseStart_696028 : Nat := 118140960795 + 696028 * 2 ^ 59
def prefixEnd_696028 : Nat := 4983230072969 + 3 ^ 40 * 696028 * 2
def baseEnd_696028 : Nat := 8824615135498963480223

theorem tailTrace_696028 : CollatzResearch.WordTrace tailWord_696028 prefixEnd_696028 8824615135498963480223 := by
  unfold tailWord_696028
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693113361208451481808369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16924151148277935309077825 12693113361208451481808369)
  ·
    refine ⟨9519835020906338611356277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12693113361208451481808369 9519835020906338611356277)
    ·
      refine ⟨892484533209969244814651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9519835020906338611356277 892484533209969244814651)
      ·
        refine ⟨1338726799814953867221977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892484533209969244814651 1338726799814953867221977)
        ·
          refine ⟨1004045099861215400416483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338726799814953867221977 1004045099861215400416483)
          ·
            refine ⟨1506067649791823100624725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004045099861215400416483 1506067649791823100624725)
            ·
              refine ⟨8824615135498963480223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1506067649791823100624725 8824615135498963480223)
              ·
                rfl

theorem cell22_696028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 9].length) (baseStart_696028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696028 prefixEnd_696028 := by exact prefixLift 696028
  have htrace : WordTrace (prefixWord ++ tailWord_696028) baseStart_696028 baseEnd_696028 := by
    simpa [prefixWord, tailWord_696028, baseEnd_696028] using wordTrace_append hprefix tailTrace_696028
  have hstable : (prefixWord ++ tailWord_696028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696028).length < 2 ^ (prefixWord ++ tailWord_696028).sum := by decide
  have hdescent : baseEnd_696028 < baseStart_696028 := by decide
  rcases family_descends (prefixWord ++ tailWord_696028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696062 : List Nat := [4, 2, 2, 1, 4, 1, 2, 6]
def baseStart_696062 : Nat := 118140960795 + 696062 * 2 ^ 59
def prefixEnd_696062 : Nat := 4983230072969 + 3 ^ 40 * 696062 * 2
def baseEnd_696062 : Nat := 26475138617034139846213

theorem tailTrace_696062 : CollatzResearch.WordTrace tailWord_696062 prefixEnd_696062 26475138617034139846213 := by
  unfold tailWord_696062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173433350536715846294305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16924977869529151180236293 3173433350536715846294305)
  ·
    refine ⟨2380075012902536884720729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3173433350536715846294305 2380075012902536884720729)
    ·
      refine ⟨1785056259676902663540547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2380075012902536884720729 1785056259676902663540547)
      ·
        refine ⟨2677584389515353995310821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785056259676902663540547 2677584389515353995310821)
        ·
          refine ⟨502047073034128874120779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2677584389515353995310821 502047073034128874120779)
          ·
            refine ⟨753070609551193311181169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502047073034128874120779 753070609551193311181169)
            ·
              refine ⟨564802957163394983385877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753070609551193311181169 564802957163394983385877)
              ·
                refine ⟨26475138617034139846213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564802957163394983385877 26475138617034139846213)
                ·
                  rfl

theorem cell22_696062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_696062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696062 prefixEnd_696062 := by exact prefixLift 696062
  have htrace : WordTrace (prefixWord ++ tailWord_696062) baseStart_696062 baseEnd_696062 := by
    simpa [prefixWord, tailWord_696062, baseEnd_696062] using wordTrace_append hprefix tailTrace_696062
  have hstable : (prefixWord ++ tailWord_696062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696062).length < 2 ^ (prefixWord ++ tailWord_696062).sum := by decide
  have hdescent : baseEnd_696062 < baseStart_696062 := by decide
  rcases family_descends (prefixWord ++ tailWord_696062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696120 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_696120 : Nat := 118140960795 + 696120 * 2 ^ 59
def prefixEnd_696120 : Nat := 4983230072969 + 3 ^ 40 * 696120 * 2
def baseEnd_696120 : Nat := 238296102138614440665739

theorem tailTrace_696120 : CollatzResearch.WordTrace tailWord_696120 prefixEnd_696120 238296102138614440665739 := by
  unfold tailWord_696120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12694791119041801337982907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16926388158722401783977209 12694791119041801337982907)
  ·
    refine ⟨19042186678562702006974361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12694791119041801337982907 19042186678562702006974361)
    ·
      refine ⟨14281640008922026505230771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19042186678562702006974361 14281640008922026505230771)
      ·
        refine ⟨21422460013383039757846157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14281640008922026505230771 21422460013383039757846157)
        ·
          refine ⟨8033422505018639909192309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21422460013383039757846157 8033422505018639909192309)
          ·
            refine ⟨753133359845497491486779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8033422505018639909192309 753133359845497491486779)
            ·
              refine ⟨1129700039768246237230169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753133359845497491486779 1129700039768246237230169)
              ·
                refine ⟨847275029826184677922627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129700039768246237230169 847275029826184677922627)
                ·
                  refine ⟨1270912544739277016883941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847275029826184677922627 1270912544739277016883941)
                  ·
                    refine ⟨238296102138614440665739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270912544739277016883941 238296102138614440665739)
                    ·
                      rfl

theorem cell22_696120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_696120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696120 prefixEnd_696120 := by exact prefixLift 696120
  have htrace : WordTrace (prefixWord ++ tailWord_696120) baseStart_696120 baseEnd_696120 := by
    simpa [prefixWord, tailWord_696120, baseEnd_696120] using wordTrace_append hprefix tailTrace_696120
  have hstable : (prefixWord ++ tailWord_696120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696120).length < 2 ^ (prefixWord ++ tailWord_696120).sum := by decide
  have hdescent : baseEnd_696120 < baseStart_696120 := by decide
  rcases family_descends (prefixWord ++ tailWord_696120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696146 : List Nat := [3, 2, 2, 1, 1, 13]
def baseStart_696146 : Nat := 118140960795 + 696146 * 2 ^ 59
def prefixEnd_696146 : Nat := 4983230072969 + 3 ^ 40 * 696146 * 2
def baseEnd_696146 : Nat := 2942037067530358512539

theorem tailTrace_696146 : CollatzResearch.WordTrace tailWord_696146 prefixEnd_696146 2942037067530358512539 := by
  unfold tailWord_696146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347632633997352279103073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16927020357326272744274861 6347632633997352279103073)
  ·
    refine ⟨4760724475498014209327305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6347632633997352279103073 4760724475498014209327305)
    ·
      refine ⟨3570543356623510656995479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4760724475498014209327305 3570543356623510656995479)
      ·
        refine ⟨5355815034935265985493219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3570543356623510656995479 5355815034935265985493219)
        ·
          refine ⟨8033722552402898978239829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355815034935265985493219 8033722552402898978239829)
          ·
            refine ⟨2942037067530358512539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 8033722552402898978239829 2942037067530358512539)
            ·
              rfl

theorem cell22_696146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 13].length) (baseStart_696146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696146 prefixEnd_696146 := by exact prefixLift 696146
  have htrace : WordTrace (prefixWord ++ tailWord_696146) baseStart_696146 baseEnd_696146 := by
    simpa [prefixWord, tailWord_696146, baseEnd_696146] using wordTrace_append hprefix tailTrace_696146
  have hstable : (prefixWord ++ tailWord_696146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696146).length < 2 ^ (prefixWord ++ tailWord_696146).sum := by decide
  have hdescent : baseEnd_696146 < baseStart_696146 := by decide
  rcases family_descends (prefixWord ++ tailWord_696146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696176 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_696176 : Nat := 118140960795 + 696176 * 2 ^ 59
def prefixEnd_696176 : Nat := 4983230072969 + 3 ^ 40 * 696176 * 2
def baseEnd_696176 : Nat := 238315272083048961265567

theorem tailTrace_696176 : CollatzResearch.WordTrace tailWord_696176 prefixEnd_696176 238315272083048961265567 := by
  unfold tailWord_696176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12695812362940362120002191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16927749817253816160002921 12695812362940362120002191)
  ·
    refine ⟨19043718544410543180003287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12695812362940362120002191 19043718544410543180003287)
    ·
      refine ⟨28565577816615814770004931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19043718544410543180003287 28565577816615814770004931)
      ·
        refine ⟨42848366724923722155007397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28565577816615814770004931 42848366724923722155007397)
        ·
          refine ⟨8034068760923197904063887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42848366724923722155007397 8034068760923197904063887)
          ·
            refine ⟨12051103141384796856095831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034068760923197904063887 12051103141384796856095831)
            ·
              refine ⟨18076654712077195284143747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12051103141384796856095831 18076654712077195284143747)
              ·
                refine ⟨27114982068115792926215621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18076654712077195284143747 27114982068115792926215621)
                ·
                  refine ⟨5084059137771711173665429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27114982068115792926215621 5084059137771711173665429)
                  ·
                    refine ⟨238315272083048961265567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5084059137771711173665429 238315272083048961265567)
                    ·
                      rfl

theorem cell22_696176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_696176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696176 prefixEnd_696176 := by exact prefixLift 696176
  have htrace : WordTrace (prefixWord ++ tailWord_696176) baseStart_696176 baseEnd_696176 := by
    simpa [prefixWord, tailWord_696176, baseEnd_696176] using wordTrace_append hprefix tailTrace_696176
  have hstable : (prefixWord ++ tailWord_696176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696176).length < 2 ^ (prefixWord ++ tailWord_696176).sum := by decide
  have hdescent : baseEnd_696176 < baseStart_696176 := by decide
  rcases family_descends (prefixWord ++ tailWord_696176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696191 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 7]
def baseStart_696191 : Nat := 118140960795 + 696191 * 2 ^ 59
def prefixEnd_696191 : Nat := 4983230072969 + 3 ^ 40 * 696191 * 2
def baseEnd_696191 : Nat := 79440135629864640713507

theorem tailTrace_696191 : CollatzResearch.WordTrace tailWord_696191 prefixEnd_696191 79440135629864640713507 := by
  unfold tailWord_696191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25392171820826381801800427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16928114547217587867866951 25392171820826381801800427)
  ·
    refine ⟨38088257731239572702700641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25392171820826381801800427 38088257731239572702700641)
    ·
      refine ⟨28566193298429679527025481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38088257731239572702700641 28566193298429679527025481)
      ·
        refine ⟨21424644973822259645269111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28566193298429679527025481 21424644973822259645269111)
        ·
          refine ⟨32136967460733389467903667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21424644973822259645269111 32136967460733389467903667)
          ·
            refine ⟨48205451191100084201855501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32136967460733389467903667 48205451191100084201855501)
            ·
              refine ⟨18077044196662531575695813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48205451191100084201855501 18077044196662531575695813)
              ·
                refine ⟨3389445786874224670442965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18077044196662531575695813 3389445786874224670442965)
                ·
                  refine ⟨79440135629864640713507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3389445786874224670442965 79440135629864640713507)
                  ·
                    rfl

theorem cell22_696191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_696191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696191 prefixEnd_696191 := by exact prefixLift 696191
  have htrace : WordTrace (prefixWord ++ tailWord_696191) baseStart_696191 baseEnd_696191 := by
    simpa [prefixWord, tailWord_696191, baseEnd_696191] using wordTrace_append hprefix tailTrace_696191
  have hstable : (prefixWord ++ tailWord_696191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696191).length < 2 ^ (prefixWord ++ tailWord_696191).sum := by decide
  have hdescent : baseEnd_696191 < baseStart_696191 := by decide
  rcases family_descends (prefixWord ++ tailWord_696191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696212 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_696212 : Nat := 118140960795 + 696212 * 2 ^ 59
def prefixEnd_696212 : Nat := 4983230072969 + 3 ^ 40 * 696212 * 2
def baseEnd_696212 : Nat := 238327595618756867365457

theorem tailTrace_696212 : CollatzResearch.WordTrace tailWord_696212 prefixEnd_696212 238327595618756867365457 := by
  unfold tailWord_696212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12696468876875151194157445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16928625169166868258876593 12696468876875151194157445)
  ·
    refine ⟨2380587914414090848904521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12696468876875151194157445 2380587914414090848904521)
    ·
      refine ⟨1785440935810568136678391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2380587914414090848904521 1785440935810568136678391)
      ·
        refine ⟨2678161403715852205017587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785440935810568136678391 2678161403715852205017587)
        ·
          refine ⟨4017242105573778307526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678161403715852205017587 4017242105573778307526381)
          ·
            refine ⟨1506465789590166865322393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4017242105573778307526381 1506465789590166865322393)
            ·
              refine ⟨1129849342192625148991795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506465789590166865322393 1129849342192625148991795)
              ·
                refine ⟨1694774013288937723487693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129849342192625148991795 1694774013288937723487693)
                ·
                  refine ⟨635540254983351646307885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1694774013288937723487693 635540254983351646307885)
                  ·
                    refine ⟨238327595618756867365457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635540254983351646307885 238327595618756867365457)
                    ·
                      rfl

theorem cell22_696212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_696212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696212 prefixEnd_696212 := by exact prefixLift 696212
  have htrace : WordTrace (prefixWord ++ tailWord_696212) baseStart_696212 baseEnd_696212 := by
    simpa [prefixWord, tailWord_696212, baseEnd_696212] using wordTrace_append hprefix tailTrace_696212
  have hstable : (prefixWord ++ tailWord_696212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696212).length < 2 ^ (prefixWord ++ tailWord_696212).sum := by decide
  have hdescent : baseEnd_696212 < baseStart_696212 := by decide
  rcases family_descends (prefixWord ++ tailWord_696212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696298 : List Nat := [3, 1, 3, 1, 2, 1, 1, 10]
def baseStart_696298 : Nat := 118140960795 + 696298 * 2 ^ 59
def prefixEnd_696298 : Nat := 4983230072969 + 3 ^ 40 * 696298 * 2
def baseEnd_696298 : Nat := 26484115019586812190577

theorem tailTrace_696298 : CollatzResearch.WordTrace tailWord_696298 prefixEnd_696298 26484115019586812190577 := by
  unfold tailWord_696298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349018607859684768986387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16930716287625826050630365 6349018607859684768986387)
  ·
    refine ⟨9523527911789527153479581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349018607859684768986387 9523527911789527153479581)
    ·
      refine ⟨3571322966921072682554843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9523527911789527153479581 3571322966921072682554843)
      ·
        refine ⟨5356984450381609023832265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571322966921072682554843 5356984450381609023832265)
        ·
          refine ⟨4017738337786206767874199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5356984450381609023832265 4017738337786206767874199)
          ·
            refine ⟨6026607506679310151811299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017738337786206767874199 6026607506679310151811299)
            ·
              refine ⟨9039911260018965227716949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026607506679310151811299 9039911260018965227716949)
              ·
                refine ⟨26484115019586812190577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9039911260018965227716949 26484115019586812190577)
                ·
                  rfl

theorem cell22_696298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_696298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696298 prefixEnd_696298 := by exact prefixLift 696298
  have htrace : WordTrace (prefixWord ++ tailWord_696298) baseStart_696298 baseEnd_696298 := by
    simpa [prefixWord, tailWord_696298, baseEnd_696298] using wordTrace_append hprefix tailTrace_696298
  have hstable : (prefixWord ++ tailWord_696298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696298).length < 2 ^ (prefixWord ++ tailWord_696298).sum := by decide
  have hdescent : baseEnd_696298 < baseStart_696298 := by decide
  rcases family_descends (prefixWord ++ tailWord_696298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696328 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_696328 : Nat := 118140960795 + 696328 * 2 ^ 59
def prefixEnd_696328 : Nat := 4983230072969 + 3 ^ 40 * 696328 * 2
def baseEnd_696328 : Nat := 238367304789371231465101

theorem tailTrace_696328 : CollatzResearch.WordTrace tailWord_696328 prefixEnd_696328 238367304789371231465101 := by
  unfold tailWord_696328
  simp only [CollatzResearch.WordTrace]
  refine ⟨12698584310665027099768819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16931445747553369466358425 12698584310665027099768819)
  ·
    refine ⟨19047876465997540649653229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12698584310665027099768819 19047876465997540649653229)
    ·
      refine ⟨7142953674749077743619961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19047876465997540649653229 7142953674749077743619961)
      ·
        refine ⟨5357215256061808307714971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7142953674749077743619961 5357215256061808307714971)
        ·
          refine ⟨8035822884092712461572457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357215256061808307714971 8035822884092712461572457)
          ·
            refine ⟨6026867163069534346179343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8035822884092712461572457 6026867163069534346179343)
            ·
              refine ⟨9040300744604301519269015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026867163069534346179343 9040300744604301519269015)
              ·
                refine ⟨13560451116906452278903523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9040300744604301519269015 13560451116906452278903523)
                ·
                  refine ⟨20340676675359678418355285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13560451116906452278903523 20340676675359678418355285)
                  ·
                    refine ⟨238367304789371231465101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20340676675359678418355285 238367304789371231465101)
                    ·
                      rfl

theorem cell22_696328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_696328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696328 prefixEnd_696328 := by exact prefixLift 696328
  have htrace : WordTrace (prefixWord ++ tailWord_696328) baseStart_696328 baseEnd_696328 := by
    simpa [prefixWord, tailWord_696328, baseEnd_696328] using wordTrace_append hprefix tailTrace_696328
  have hstable : (prefixWord ++ tailWord_696328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696328).length < 2 ^ (prefixWord ++ tailWord_696328).sum := by decide
  have hdescent : baseEnd_696328 < baseStart_696328 := by decide
  rcases family_descends (prefixWord ++ tailWord_696328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696405 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 6]
def baseStart_696405 : Nat := 118140960795 + 696405 * 2 ^ 59
def prefixEnd_696405 : Nat := 4983230072969 + 3 ^ 40 * 696405 * 2
def baseEnd_696405 : Nat := 79464554487656232429955

theorem tailTrace_696405 : CollatzResearch.WordTrace tailWord_696405 prefixEnd_696405 79464554487656232429955 := by
  unfold tailWord_696405
  simp only [CollatzResearch.WordTrace]
  refine ⟨25399977042051096350090669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16933318028034064233393779 25399977042051096350090669)
  ·
    refine ⟨9524991390769161131284001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25399977042051096350090669 9524991390769161131284001)
    ·
      refine ⟨7143743543076870848463001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9524991390769161131284001 7143743543076870848463001)
      ·
        refine ⟨5357807657307653136347251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7143743543076870848463001 5357807657307653136347251)
        ·
          refine ⟨8036711485961479704520877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357807657307653136347251 8036711485961479704520877)
          ·
            refine ⟨3013766807235554889195329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8036711485961479704520877 3013766807235554889195329)
            ·
              refine ⟨2260325105426666166896497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013766807235554889195329 2260325105426666166896497)
              ·
                refine ⟨1695243829069999625172373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260325105426666166896497 1695243829069999625172373)
                ·
                  refine ⟨79464554487656232429955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1695243829069999625172373 79464554487656232429955)
                  ·
                    rfl

theorem cell22_696405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_696405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696405 prefixEnd_696405 := by exact prefixLift 696405
  have htrace : WordTrace (prefixWord ++ tailWord_696405) baseStart_696405 baseEnd_696405 := by
    simpa [prefixWord, tailWord_696405, baseEnd_696405] using wordTrace_append hprefix tailTrace_696405
  have hstable : (prefixWord ++ tailWord_696405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696405).length < 2 ^ (prefixWord ++ tailWord_696405).sum := by decide
  have hdescent : baseEnd_696405 < baseStart_696405 := by decide
  rcases family_descends (prefixWord ++ tailWord_696405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696420 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_696420 : Nat := 118140960795 + 696420 * 2 ^ 59
def prefixEnd_696420 : Nat := 4983230072969 + 3 ^ 40 * 696420 * 2
def baseEnd_696420 : Nat := 238398798269513658164819

theorem tailTrace_696420 : CollatzResearch.WordTrace tailWord_696420 prefixEnd_696420 238398798269513658164819 := by
  unfold tailWord_696420
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700262068498376955943357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16933682757997835941257809 12700262068498376955943357)
  ·
    refine ⟨4762598275686891358478759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12700262068498376955943357 4762598275686891358478759)
    ·
      refine ⟨7143897413530337037718139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4762598275686891358478759 7143897413530337037718139)
      ·
        refine ⟨10715846120295505556577209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143897413530337037718139 10715846120295505556577209)
        ·
          refine ⟨8036884590221629167432907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10715846120295505556577209 8036884590221629167432907)
          ·
            refine ⟨12055326885332443751149361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8036884590221629167432907 12055326885332443751149361)
            ·
              refine ⟨9041495163999332813362021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12055326885332443751149361 9041495163999332813362021)
              ·
                refine ⟨1695280343249874902505379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9041495163999332813362021 1695280343249874902505379)
                ·
                  refine ⟨2542920514874812353758069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695280343249874902505379 2542920514874812353758069)
                  ·
                    refine ⟨238398798269513658164819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2542920514874812353758069 238398798269513658164819)
                    ·
                      rfl

theorem cell22_696420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_696420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696420 prefixEnd_696420 := by exact prefixLift 696420
  have htrace : WordTrace (prefixWord ++ tailWord_696420) baseStart_696420 baseEnd_696420 := by
    simpa [prefixWord, tailWord_696420, baseEnd_696420] using wordTrace_append hprefix tailTrace_696420
  have hstable : (prefixWord ++ tailWord_696420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696420).length < 2 ^ (prefixWord ++ tailWord_696420).sum := by decide
  have hdescent : baseEnd_696420 < baseStart_696420 := by decide
  rcases family_descends (prefixWord ++ tailWord_696420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696439 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 4]
def baseStart_696439 : Nat := 118140960795 + 696439 * 2 ^ 59
def prefixEnd_696439 : Nat := 4983230072969 + 3 ^ 40 * 696439 * 2
def baseEnd_696439 : Nat := 79468434119267980646587

theorem tailTrace_696439 : CollatzResearch.WordTrace tailWord_696439 prefixEnd_696439 79468434119267980646587 := by
  unfold tailWord_696439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401217123927920156828371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16934144749285280104552247 25401217123927920156828371)
  ·
    refine ⟨38101825685891880235242557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25401217123927920156828371 38101825685891880235242557)
    ·
      refine ⟨14288184632209455088215959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38101825685891880235242557 14288184632209455088215959)
      ·
        refine ⟨21432276948314182632323939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14288184632209455088215959 21432276948314182632323939)
        ·
          refine ⟨32148415422471273948485909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21432276948314182632323939 32148415422471273948485909)
          ·
            refine ⟨1506956972928340966335277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32148415422471273948485909 1506956972928340966335277)
            ·
              refine ⟨565108864848127862375729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1506956972928340966335277 565108864848127862375729)
              ·
                refine ⟨423831648636095896781797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565108864848127862375729 423831648636095896781797)
                ·
                  refine ⟨79468434119267980646587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423831648636095896781797 79468434119267980646587)
                  ·
                    rfl

theorem cell22_696439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 4].length) (baseStart_696439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696439 prefixEnd_696439 := by exact prefixLift 696439
  have htrace : WordTrace (prefixWord ++ tailWord_696439) baseStart_696439 baseEnd_696439 := by
    simpa [prefixWord, tailWord_696439, baseEnd_696439] using wordTrace_append hprefix tailTrace_696439
  have hstable : (prefixWord ++ tailWord_696439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696439).length < 2 ^ (prefixWord ++ tailWord_696439).sum := by decide
  have hdescent : baseEnd_696439 < baseStart_696439 := by decide
  rcases family_descends (prefixWord ++ tailWord_696439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696490 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_696490 : Nat := 118140960795 + 696490 * 2 ^ 59
def prefixEnd_696490 : Nat := 4983230072969 + 3 ^ 40 * 696490 * 2
def baseEnd_696490 : Nat := 79474253566685602971535

theorem tailTrace_696490 : CollatzResearch.WordTrace tailWord_696490 prefixEnd_696490 79474253566685602971535 := by
  unfold tailWord_696490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350769311685788966733731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16935384831162103911289949 6350769311685788966733731)
  ·
    refine ⟨9526153967528683450100597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350769311685788966733731 9526153967528683450100597)
    ·
      refine ⟨893076934455814073446931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9526153967528683450100597 893076934455814073446931)
      ·
        refine ⟨1339615401683721110170397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893076934455814073446931 1339615401683721110170397)
        ·
          refine ⟨502355775631395416313899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1339615401683721110170397 502355775631395416313899)
          ·
            refine ⟨753533663447093124470849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502355775631395416313899 753533663447093124470849)
            ·
              refine ⟨565150247585319843353137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753533663447093124470849 565150247585319843353137)
              ·
                refine ⟨423862685688989882514853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565150247585319843353137 423862685688989882514853)
                ·
                  refine ⟨79474253566685602971535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423862685688989882514853 79474253566685602971535)
                  ·
                    rfl

theorem cell22_696490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_696490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696490 prefixEnd_696490 := by exact prefixLift 696490
  have htrace : WordTrace (prefixWord ++ tailWord_696490) baseStart_696490 baseEnd_696490 := by
    simpa [prefixWord, tailWord_696490, baseEnd_696490] using wordTrace_append hprefix tailTrace_696490
  have hstable : (prefixWord ++ tailWord_696490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696490).length < 2 ^ (prefixWord ++ tailWord_696490).sum := by decide
  have hdescent : baseEnd_696490 < baseStart_696490 := by decide
  rcases family_descends (prefixWord ++ tailWord_696490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696501 : List Nat := [1, 3, 3, 4, 2, 1, 1, 7]
def baseStart_696501 : Nat := 118140960795 + 696501 * 2 ^ 59
def prefixEnd_696501 : Nat := 4983230072969 + 3 ^ 40 * 696501 * 2
def baseEnd_696501 : Nat := 26491836247206271876619

theorem tailTrace_696501 : CollatzResearch.WordTrace tailWord_696501 prefixEnd_696501 26491836247206271876619 := by
  unfold tailWord_696501
  simp only [CollatzResearch.WordTrace]
  refine ⟨25403478449703304745585357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16935652299802203163723571 25403478449703304745585357)
  ·
    refine ⟨9526304418638739279594509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25403478449703304745585357 9526304418638739279594509)
    ·
      refine ⟨3572364156989527229847941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9526304418638739279594509 3572364156989527229847941)
      ·
        refine ⟨669818279435536355596489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3572364156989527229847941 669818279435536355596489)
        ·
          refine ⟨502363709576652266697367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669818279435536355596489 502363709576652266697367)
          ·
            refine ⟨753545564364978400046051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502363709576652266697367 753545564364978400046051)
            ·
              refine ⟨1130318346547467600069077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753545564364978400046051 1130318346547467600069077)
              ·
                refine ⟨26491836247206271876619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1130318346547467600069077 26491836247206271876619)
                ·
                  rfl

theorem cell22_696501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 7].length) (baseStart_696501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696501 prefixEnd_696501 := by exact prefixLift 696501
  have htrace : WordTrace (prefixWord ++ tailWord_696501) baseStart_696501 baseEnd_696501 := by
    simpa [prefixWord, tailWord_696501, baseEnd_696501] using wordTrace_append hprefix tailTrace_696501
  have hstable : (prefixWord ++ tailWord_696501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696501).length < 2 ^ (prefixWord ++ tailWord_696501).sum := by decide
  have hdescent : baseEnd_696501 < baseStart_696501 := by decide
  rcases family_descends (prefixWord ++ tailWord_696501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696512 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 5]
def baseStart_696512 : Nat := 118140960795 + 696512 * 2 ^ 59
def prefixEnd_696512 : Nat := 4983230072969 + 3 ^ 40 * 696512 * 2
def baseEnd_696512 : Nat := 79476763916552028288179

theorem tailTrace_696512 : CollatzResearch.WordTrace tailWord_696512 prefixEnd_696512 79476763916552028288179 := by
  unfold tailWord_696512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701939826331726812117895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16935919768442302416157193 12701939826331726812117895)
  ·
    refine ⟨19052909739497590218176843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12701939826331726812117895 19052909739497590218176843)
    ·
      refine ⟨28579364609246385327265265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19052909739497590218176843 28579364609246385327265265)
      ·
        refine ⟨21434523456934788995448949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28579364609246385327265265 21434523456934788995448949)
        ·
          refine ⟨2009486574087636468323339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21434523456934788995448949 2009486574087636468323339)
          ·
            refine ⟨3014229861131454702485009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009486574087636468323339 3014229861131454702485009)
            ·
              refine ⟨2260672395848591026863757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014229861131454702485009 2260672395848591026863757)
              ·
                refine ⟨847752148443221635073909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2260672395848591026863757 847752148443221635073909)
                ·
                  refine ⟨79476763916552028288179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 847752148443221635073909 79476763916552028288179)
                  ·
                    rfl

theorem cell22_696512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_696512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696512 prefixEnd_696512 := by exact prefixLift 696512
  have htrace : WordTrace (prefixWord ++ tailWord_696512) baseStart_696512 baseEnd_696512 := by
    simpa [prefixWord, tailWord_696512, baseEnd_696512] using wordTrace_append hprefix tailTrace_696512
  have hstable : (prefixWord ++ tailWord_696512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696512).length < 2 ^ (prefixWord ++ tailWord_696512).sum := by decide
  have hdescent : baseEnd_696512 < baseStart_696512 := by decide
  rcases family_descends (prefixWord ++ tailWord_696512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696533 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_696533 : Nat := 118140960795 + 696533 * 2 ^ 59
def prefixEnd_696533 : Nat := 4983230072969 + 3 ^ 40 * 696533 * 2
def baseEnd_696533 : Nat := 238437480478819030089473

theorem tailTrace_696533 : CollatzResearch.WordTrace tailWord_696533 prefixEnd_696533 238437480478819030089473 := by
  unfold tailWord_696533
  simp only [CollatzResearch.WordTrace]
  refine ⟨25404645585587374210750253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16936430390391582807166835 25404645585587374210750253)
  ·
    refine ⟨9526742094595265329031345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25404645585587374210750253 9526742094595265329031345)
    ·
      refine ⟨7145056570946448996773509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9526742094595265329031345 7145056570946448996773509)
      ·
        refine ⟨1339698107052459186895033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7145056570946448996773509 1339698107052459186895033)
        ·
          refine ⟨1004773580289344390171275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339698107052459186895033 1004773580289344390171275)
          ·
            refine ⟨1507160370434016585256913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004773580289344390171275 1507160370434016585256913)
            ·
              refine ⟨1130370277825512438942685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1507160370434016585256913 1130370277825512438942685)
              ·
                refine ⟨423888854184567164603507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130370277825512438942685 423888854184567164603507)
                ·
                  refine ⟨635833281276850746905261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423888854184567164603507 635833281276850746905261)
                  ·
                    refine ⟨238437480478819030089473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635833281276850746905261 238437480478819030089473)
                    ·
                      rfl

theorem cell22_696533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_696533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696533 prefixEnd_696533 := by exact prefixLift 696533
  have htrace : WordTrace (prefixWord ++ tailWord_696533) baseStart_696533 baseEnd_696533 := by
    simpa [prefixWord, tailWord_696533, baseEnd_696533] using wordTrace_append hprefix tailTrace_696533
  have hstable : (prefixWord ++ tailWord_696533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696533).length < 2 ^ (prefixWord ++ tailWord_696533).sum := by decide
  have hdescent : baseEnd_696533 < baseStart_696533 := by decide
  rcases family_descends (prefixWord ++ tailWord_696533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696587 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_696587 : Nat := 118140960795 + 696587 * 2 ^ 59
def prefixEnd_696587 : Nat := 4983230072969 + 3 ^ 40 * 696587 * 2
def baseEnd_696587 : Nat := 238455965782380889239307

theorem tailTrace_696587 : CollatzResearch.WordTrace tailWord_696587 prefixEnd_696587 238455965782380889239307 := by
  unfold tailWord_696587
  simp only [CollatzResearch.WordTrace]
  refine ⟨25406615127391741433216015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16937743418261160955477343 25406615127391741433216015)
  ·
    refine ⟨38109922691087612149824023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25406615127391741433216015 38109922691087612149824023)
    ·
      refine ⟨57164884036631418224736035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38109922691087612149824023 57164884036631418224736035)
      ·
        refine ⟨85747326054947127337104053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57164884036631418224736035 85747326054947127337104053)
        ·
          refine ⟨8038811817651293187853505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85747326054947127337104053 8038811817651293187853505)
          ·
            refine ⟨6029108863238469890890129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8038811817651293187853505 6029108863238469890890129)
            ·
              refine ⟨4521831647428852418167597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6029108863238469890890129 4521831647428852418167597)
              ·
                refine ⟨1695686867785819656812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4521831647428852418167597 1695686867785819656812849)
                ·
                  refine ⟨1271765150839364742609637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695686867785819656812849 1271765150839364742609637)
                  ·
                    refine ⟨238455965782380889239307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1271765150839364742609637 238455965782380889239307)
                    ·
                      rfl

theorem cell22_696587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_696587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696587 prefixEnd_696587 := by exact prefixLift 696587
  have htrace : WordTrace (prefixWord ++ tailWord_696587) baseStart_696587 baseEnd_696587 := by
    simpa [prefixWord, tailWord_696587, baseEnd_696587] using wordTrace_append hprefix tailTrace_696587
  have hstable : (prefixWord ++ tailWord_696587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696587).length < 2 ^ (prefixWord ++ tailWord_696587).sum := by decide
  have hdescent : baseEnd_696587 < baseStart_696587 := by decide
  rcases family_descends (prefixWord ++ tailWord_696587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696679 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_696679 : Nat := 118140960795 + 696679 * 2 ^ 59
def prefixEnd_696679 : Nat := 4983230072969 + 3 ^ 40 * 696679 * 2
def baseEnd_696679 : Nat := 238487459262523315939025

theorem tailTrace_696679 : CollatzResearch.WordTrace tailWord_696679 prefixEnd_696679 238487459262523315939025 := by
  unfold tailWord_696679
  simp only [CollatzResearch.WordTrace]
  refine ⟨25409970643058441145565091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16939980428705627430376727 25409970643058441145565091)
  ·
    refine ⟨38114955964587661718347637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25409970643058441145565091 38114955964587661718347637)
    ·
      refine ⟨3573277121680093286095091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38114955964587661718347637 3573277121680093286095091)
      ·
        refine ⟨5359915682520139929142637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573277121680093286095091 5359915682520139929142637)
        ·
          refine ⟨2009968380945052473428489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5359915682520139929142637 2009968380945052473428489)
          ·
            refine ⟨1507476285708789355071367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009968380945052473428489 1507476285708789355071367)
            ·
              refine ⟨2261214428563184032607051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507476285708789355071367 2261214428563184032607051)
              ·
                refine ⟨3391821642844776048910577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261214428563184032607051 3391821642844776048910577)
                ·
                  refine ⟨2543866232133582036682933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3391821642844776048910577 2543866232133582036682933)
                  ·
                    refine ⟨238487459262523315939025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2543866232133582036682933 238487459262523315939025)
                    ·
                      rfl

theorem cell22_696679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_696679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696679 prefixEnd_696679 := by exact prefixLift 696679
  have htrace : WordTrace (prefixWord ++ tailWord_696679) baseStart_696679 baseEnd_696679 := by
    simpa [prefixWord, tailWord_696679, baseEnd_696679] using wordTrace_append hprefix tailTrace_696679
  have hstable : (prefixWord ++ tailWord_696679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696679).length < 2 ^ (prefixWord ++ tailWord_696679).sum := by decide
  have hdescent : baseEnd_696679 < baseStart_696679 := by decide
  rcases family_descends (prefixWord ++ tailWord_696679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696767 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_696767 : Nat := 118140960795 + 696767 * 2 ^ 59
def prefixEnd_696767 : Nat := 4983230072969 + 3 ^ 40 * 696767 * 2
def baseEnd_696767 : Nat := 238517583460920419738755

theorem tailTrace_696767 : CollatzResearch.WordTrace tailWord_696767 prefixEnd_696767 238517583460920419738755 := by
  unfold tailWord_696767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413180266739632174768555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16942120177826421449845703 25413180266739632174768555)
  ·
    refine ⟨38119770400109448262152833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25413180266739632174768555 38119770400109448262152833)
    ·
      refine ⟨28589827800082086196614625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38119770400109448262152833 28589827800082086196614625)
      ·
        refine ⟨21442370850061564647460969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28589827800082086196614625 21442370850061564647460969)
        ·
          refine ⟨16081778137546173485595727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21442370850061564647460969 16081778137546173485595727)
          ·
            refine ⟨24122667206319260228393591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16081778137546173485595727 24122667206319260228393591)
            ·
              refine ⟨36184000809478890342590387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24122667206319260228393591 36184000809478890342590387)
              ·
                refine ⟨54276001214218335513885581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36184000809478890342590387 54276001214218335513885581)
                ·
                  refine ⟨20353500455331875817707093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54276001214218335513885581 20353500455331875817707093)
                  ·
                    refine ⟨238517583460920419738755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20353500455331875817707093 238517583460920419738755)
                    ·
                      rfl

theorem cell22_696767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_696767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696767 prefixEnd_696767 := by exact prefixLift 696767
  have htrace : WordTrace (prefixWord ++ tailWord_696767) baseStart_696767 baseEnd_696767 := by
    simpa [prefixWord, tailWord_696767, baseEnd_696767] using wordTrace_append hprefix tailTrace_696767
  have hstable : (prefixWord ++ tailWord_696767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696767).length < 2 ^ (prefixWord ++ tailWord_696767).sum := by decide
  have hdescent : baseEnd_696767 < baseStart_696767 := by decide
  rcases family_descends (prefixWord ++ tailWord_696767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696846 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_696846 : Nat := 118140960795 + 696846 * 2 ^ 59
def prefixEnd_696846 : Nat := 4983230072969 + 3 ^ 40 * 696846 * 2
def baseEnd_696846 : Nat := 238544626775390547013513

theorem tailTrace_696846 : CollatzResearch.WordTrace tailWord_696846 prefixEnd_696846 238544626775390547013513 := by
  unfold tailWord_696846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177007704181678583361799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16944041088968952444596261 3177007704181678583361799)
  ·
    refine ⟨4765511556272517875042699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3177007704181678583361799 4765511556272517875042699)
    ·
      refine ⟨7148267334408776812564049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765511556272517875042699 7148267334408776812564049)
      ·
        refine ⟨5361200500806582609423037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7148267334408776812564049 5361200500806582609423037)
        ·
          refine ⟨2010450187802468478533639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5361200500806582609423037 2010450187802468478533639)
          ·
            refine ⟨3015675281703702717800459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010450187802468478533639 3015675281703702717800459)
            ·
              refine ⟨4523512922555554076700689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015675281703702717800459 4523512922555554076700689)
              ·
                refine ⟨3392634691916665557525517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523512922555554076700689 3392634691916665557525517)
                ·
                  refine ⟨1272238009468749584072069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3392634691916665557525517 1272238009468749584072069)
                  ·
                    refine ⟨238544626775390547013513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272238009468749584072069 238544626775390547013513)
                    ·
                      rfl

theorem cell22_696846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_696846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696846 prefixEnd_696846 := by exact prefixLift 696846
  have htrace : WordTrace (prefixWord ++ tailWord_696846) baseStart_696846 baseEnd_696846 := by
    simpa [prefixWord, tailWord_696846, baseEnd_696846] using wordTrace_append hprefix tailTrace_696846
  have hstable : (prefixWord ++ tailWord_696846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696846).length < 2 ^ (prefixWord ++ tailWord_696846).sum := by decide
  have hdescent : baseEnd_696846 < baseStart_696846 := by decide
  rcases family_descends (prefixWord ++ tailWord_696846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696861 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 6]
def baseStart_696861 : Nat := 118140960795 + 696861 * 2 ^ 59
def prefixEnd_696861 : Nat := 4983230072969 + 3 ^ 40 * 696861 * 2
def baseEnd_696861 : Nat := 79516587193978502629489

theorem tailTrace_696861 : CollatzResearch.WordTrace tailWord_696861 prefixEnd_696861 79516587193978502629489 := by
  unfold tailWord_696861
  simp only [CollatzResearch.WordTrace]
  refine ⟨25416608728399086228690437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16944405818932724152460291 25416608728399086228690437)
  ·
    refine ⟨4765614136574828667879457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25416608728399086228690437 4765614136574828667879457)
    ·
      refine ⟨3574210602431121500909593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4765614136574828667879457 3574210602431121500909593)
      ·
        refine ⟨2680657951823341125682195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3574210602431121500909593 2680657951823341125682195)
        ·
          refine ⟨4020986927735011688523293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680657951823341125682195 4020986927735011688523293)
          ·
            refine ⟨1507870097900629383196235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4020986927735011688523293 1507870097900629383196235)
            ·
              refine ⟨2261805146850944074794353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507870097900629383196235 2261805146850944074794353)
              ·
                refine ⟨1696353860138208056095765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261805146850944074794353 1696353860138208056095765)
                ·
                  refine ⟨79516587193978502629489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1696353860138208056095765 79516587193978502629489)
                  ·
                    rfl

theorem cell22_696861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_696861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696861 prefixEnd_696861 := by exact prefixLift 696861
  have htrace : WordTrace (prefixWord ++ tailWord_696861) baseStart_696861 baseEnd_696861 := by
    simpa [prefixWord, tailWord_696861, baseEnd_696861] using wordTrace_append hprefix tailTrace_696861
  have hstable : (prefixWord ++ tailWord_696861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696861).length < 2 ^ (prefixWord ++ tailWord_696861).sum := by decide
  have hdescent : baseEnd_696861 < baseStart_696861 := by decide
  rcases family_descends (prefixWord ++ tailWord_696861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696889 : List Nat := [1, 2, 1, 5, 1, 1, 11]
def baseStart_696889 : Nat := 118140960795 + 696889 * 2 ^ 59
def prefixEnd_696889 : Nat := 4983230072969 + 3 ^ 40 * 696889 * 2
def baseEnd_696889 : Nat := 8835531353857509932903

theorem tailTrace_696889 : CollatzResearch.WordTrace tailWord_696889 prefixEnd_696889 8835531353857509932903 := by
  unfold tailWord_696889
  simp only [CollatzResearch.WordTrace]
  refine ⟨25417629972297647010709721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16945086648198431340473147 25417629972297647010709721)
  ·
    refine ⟨19063222479223235258032291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25417629972297647010709721 19063222479223235258032291)
    ·
      refine ⟨28594833718834852887048437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19063222479223235258032291 28594833718834852887048437)
      ·
        refine ⟨2680765661140767458160791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28594833718834852887048437 2680765661140767458160791)
        ·
          refine ⟨4021148491711151187241187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680765661140767458160791 4021148491711151187241187)
          ·
            refine ⟨6031722737566726780861781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021148491711151187241187 6031722737566726780861781)
            ·
              refine ⟨8835531353857509932903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6031722737566726780861781 8835531353857509932903)
              ·
                rfl

theorem cell22_696889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 11].length) (baseStart_696889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696889 prefixEnd_696889 := by exact prefixLift 696889
  have htrace : WordTrace (prefixWord ++ tailWord_696889) baseStart_696889 baseEnd_696889 := by
    simpa [prefixWord, tailWord_696889, baseEnd_696889] using wordTrace_append hprefix tailTrace_696889
  have hstable : (prefixWord ++ tailWord_696889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696889).length < 2 ^ (prefixWord ++ tailWord_696889).sum := by decide
  have hdescent : baseEnd_696889 < baseStart_696889 := by decide
  rcases family_descends (prefixWord ++ tailWord_696889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696893 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_696893 : Nat := 118140960795 + 696893 * 2 ^ 59
def prefixEnd_696893 : Nat := 4983230072969 + 3 ^ 40 * 696893 * 2
def baseEnd_696893 : Nat := 238560715835898091088369

theorem tailTrace_696893 : CollatzResearch.WordTrace tailWord_696893 prefixEnd_696893 238560715835898091088369 := by
  unfold tailWord_696893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25417775864283155693855333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16945183909522103795903555 25417775864283155693855333)
  ·
    refine ⟨4765832974553091692597875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25417775864283155693855333 4765832974553091692597875)
    ·
      refine ⟨7148749461829637538896813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765832974553091692597875 7148749461829637538896813)
      ·
        refine ⟨2680781048186114077086305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7148749461829637538896813 2680781048186114077086305)
        ·
          refine ⟨2010585786139585557814729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680781048186114077086305 2010585786139585557814729)
          ·
            refine ⟨1507939339604689168361047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2010585786139585557814729 1507939339604689168361047)
            ·
              refine ⟨2261909009407033752541571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507939339604689168361047 2261909009407033752541571)
              ·
                refine ⟨3392863514110550628812357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261909009407033752541571 3392863514110550628812357)
                ·
                  refine ⟨636161908895728242902317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3392863514110550628812357 636161908895728242902317)
                  ·
                    refine ⟨238560715835898091088369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636161908895728242902317 238560715835898091088369)
                    ·
                      rfl

theorem cell22_696893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_696893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_696893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_696893 prefixEnd_696893 := by exact prefixLift 696893
  have htrace : WordTrace (prefixWord ++ tailWord_696893) baseStart_696893 baseEnd_696893 := by
    simpa [prefixWord, tailWord_696893, baseEnd_696893] using wordTrace_append hprefix tailTrace_696893
  have hstable : (prefixWord ++ tailWord_696893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696893).length < 2 ^ (prefixWord ++ tailWord_696893).sum := by decide
  have hdescent : baseEnd_696893 < baseStart_696893 := by decide
  rcases family_descends (prefixWord ++ tailWord_696893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697002 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_697002 : Nat := 118140960795 + 697002 * 2 ^ 59
def prefixEnd_697002 : Nat := 4983230072969 + 3 ^ 40 * 697002 * 2
def baseEnd_697002 : Nat := 79532676254486046704345

theorem tailTrace_697002 : CollatzResearch.WordTrace tailWord_697002 prefixEnd_697002 79532676254486046704345 := by
  unfold tailWord_697002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355437855222066827393315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16947834280592178206382173 6355437855222066827393315)
  ·
    refine ⟨9533156782833100241089973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355437855222066827393315 9533156782833100241089973)
    ·
      refine ⟨893733448390603147602185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9533156782833100241089973 893733448390603147602185)
      ·
        refine ⟨670300086292952360701639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893733448390603147602185 670300086292952360701639)
        ·
          refine ⟨1005450129439428541052459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670300086292952360701639 1005450129439428541052459)
          ·
            refine ⟨1508175194159142811578689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005450129439428541052459 1508175194159142811578689)
            ·
              refine ⟨1131131395619357108684017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508175194159142811578689 1131131395619357108684017)
              ·
                refine ⟨848348546714517831513013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131131395619357108684017 848348546714517831513013)
                ·
                  refine ⟨79532676254486046704345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848348546714517831513013 79532676254486046704345)
                  ·
                    rfl

theorem cell22_697002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_697002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697002 prefixEnd_697002 := by exact prefixLift 697002
  have htrace : WordTrace (prefixWord ++ tailWord_697002) baseStart_697002 baseEnd_697002 := by
    simpa [prefixWord, tailWord_697002, baseEnd_697002] using wordTrace_append hprefix tailTrace_697002
  have hstable : (prefixWord ++ tailWord_697002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697002).length < 2 ^ (prefixWord ++ tailWord_697002).sum := by decide
  have hdescent : baseEnd_697002 < baseStart_697002 := by decide
  rcases family_descends (prefixWord ++ tailWord_697002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697006 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_697006 : Nat := 118140960795 + 697006 * 2 ^ 59
def prefixEnd_697006 : Nat := 4983230072969 + 3 ^ 40 * 697006 * 2
def baseEnd_697006 : Nat := 238599398045203463013023

theorem tailTrace_697006 : CollatzResearch.WordTrace tailWord_697006 prefixEnd_697006 238599398045203463013023 := by
  unfold tailWord_697006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177737164109221999089859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16947931541915850661812581 3177737164109221999089859)
  ·
    refine ⟨4766605746163832998634789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3177737164109221999089859 4766605746163832998634789)
    ·
      refine ⟨893738577405718687244023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4766605746163832998634789 893738577405718687244023)
      ·
        refine ⟨1340607866108578030866035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893738577405718687244023 1340607866108578030866035)
        ·
          refine ⟨2010911799162867046299053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340607866108578030866035 2010911799162867046299053)
          ·
            refine ⟨754091924686075142362145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2010911799162867046299053 754091924686075142362145)
            ·
              refine ⟨565568943514556356771609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754091924686075142362145 565568943514556356771609)
              ·
                refine ⟨424176707635917267578707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565568943514556356771609 424176707635917267578707)
                ·
                  refine ⟨636265061453875901368061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424176707635917267578707 636265061453875901368061)
                  ·
                    refine ⟨238599398045203463013023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636265061453875901368061 238599398045203463013023)
                    ·
                      rfl

theorem cell22_697006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_697006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697006 prefixEnd_697006 := by exact prefixLift 697006
  have htrace : WordTrace (prefixWord ++ tailWord_697006) baseStart_697006 baseEnd_697006 := by
    simpa [prefixWord, tailWord_697006, baseEnd_697006] using wordTrace_append hprefix tailTrace_697006
  have hstable : (prefixWord ++ tailWord_697006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697006).length < 2 ^ (prefixWord ++ tailWord_697006).sum := by decide
  have hdescent : baseEnd_697006 < baseStart_697006 := by decide
  rcases family_descends (prefixWord ++ tailWord_697006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697028 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_697028 : Nat := 118140960795 + 697028 * 2 ^ 59
def prefixEnd_697028 : Nat := 4983230072969 + 3 ^ 40 * 697028 * 2
def baseEnd_697028 : Nat := 238606929094802738962955

theorem tailTrace_697028 : CollatzResearch.WordTrace tailWord_697028 prefixEnd_697028 238606929094802738962955 := by
  unfold tailWord_697028
  simp only [CollatzResearch.WordTrace]
  refine ⟨12711349859397036875009869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16948466479196049166679825 12711349859397036875009869)
  ·
    refine ⟨4766756197273888828128701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12711349859397036875009869 4766756197273888828128701)
    ·
      refine ⟨1787533573977708310548263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4766756197273888828128701 1787533573977708310548263)
      ·
        refine ⟨2681300360966562465822395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787533573977708310548263 2681300360966562465822395)
        ·
          refine ⟨4021950541449843698733593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681300360966562465822395 4021950541449843698733593)
          ·
            refine ⟨3016462906087382774050195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021950541449843698733593 3016462906087382774050195)
            ·
              refine ⟨4524694359131074161075293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016462906087382774050195 4524694359131074161075293)
              ·
                refine ⟨1696760384674152810403235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4524694359131074161075293 1696760384674152810403235)
                ·
                  refine ⟨2545140577011229215604853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696760384674152810403235 2545140577011229215604853)
                  ·
                    refine ⟨238606929094802738962955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2545140577011229215604853 238606929094802738962955)
                    ·
                      rfl

theorem cell22_697028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_697028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697028 prefixEnd_697028 := by exact prefixLift 697028
  have htrace : WordTrace (prefixWord ++ tailWord_697028) baseStart_697028 baseEnd_697028 := by
    simpa [prefixWord, tailWord_697028, baseEnd_697028] using wordTrace_append hprefix tailTrace_697028
  have hstable : (prefixWord ++ tailWord_697028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697028).length < 2 ^ (prefixWord ++ tailWord_697028).sum := by decide
  have hdescent : baseEnd_697028 < baseStart_697028 := by decide
  rcases family_descends (prefixWord ++ tailWord_697028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697124 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_697124 : Nat := 118140960795 + 697124 * 2 ^ 59
def prefixEnd_697124 : Nat := 4983230072969 + 3 ^ 40 * 697124 * 2
def baseEnd_697124 : Nat := 238639791856690488562661

theorem tailTrace_697124 : CollatzResearch.WordTrace tailWord_697124 prefixEnd_697124 238639791856690488562661 := by
  unfold tailWord_697124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12713100563223141072757213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16950800750964188097009617 12713100563223141072757213)
  ·
    refine ⟨4767412711208677902283955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12713100563223141072757213 4767412711208677902283955)
    ·
      refine ⟨7151119066813016853425933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4767412711208677902283955 7151119066813016853425933)
      ·
        refine ⟨2681669650054881320034725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7151119066813016853425933 2681669650054881320034725)
        ·
          refine ⟨502813059385290247506511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2681669650054881320034725 502813059385290247506511)
          ·
            refine ⟨754219589077935371259767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502813059385290247506511 754219589077935371259767)
            ·
              refine ⟨1131329383616903056889651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754219589077935371259767 1131329383616903056889651)
              ·
                refine ⟨1696994075425354585334477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131329383616903056889651 1696994075425354585334477)
                ·
                  refine ⟨636372778284507969500429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1696994075425354585334477 636372778284507969500429)
                  ·
                    refine ⟨238639791856690488562661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636372778284507969500429 238639791856690488562661)
                    ·
                      rfl

theorem cell22_697124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_697124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697124 prefixEnd_697124 := by exact prefixLift 697124
  have htrace : WordTrace (prefixWord ++ tailWord_697124) baseStart_697124 baseEnd_697124 := by
    simpa [prefixWord, tailWord_697124, baseEnd_697124] using wordTrace_append hprefix tailTrace_697124
  have hstable : (prefixWord ++ tailWord_697124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697124).length < 2 ^ (prefixWord ++ tailWord_697124).sum := by decide
  have hdescent : baseEnd_697124 < baseStart_697124 := by decide
  rcases family_descends (prefixWord ++ tailWord_697124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697218 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_697218 : Nat := 118140960795 + 697218 * 2 ^ 59
def prefixEnd_697218 : Nat := 4983230072969 + 3 ^ 40 * 697218 * 2
def baseEnd_697218 : Nat := 238671969977705576712373

theorem tailTrace_697218 : CollatzResearch.WordTrace tailWord_697218 prefixEnd_697218 238671969977705576712373 := by
  unfold tailWord_697218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357407397026434049859077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16953086392070490799624205 6357407397026434049859077)
  ·
    refine ⟨1192013886942456384348577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6357407397026434049859077 1192013886942456384348577)
    ·
      refine ⟨894010415206842288261433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1192013886942456384348577 894010415206842288261433)
      ·
        refine ⟨670507811405131716196075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 894010415206842288261433 670507811405131716196075)
        ·
          refine ⟨1005761717107697574294113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670507811405131716196075 1005761717107697574294113)
          ·
            refine ⟨754321287830773180720585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005761717107697574294113 754321287830773180720585)
            ·
              refine ⟨565740965873079885540439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754321287830773180720585 565740965873079885540439)
              ·
                refine ⟨848611448809619828310659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565740965873079885540439 848611448809619828310659)
                ·
                  refine ⟨1272917173214429742465989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848611448809619828310659 1272917173214429742465989)
                  ·
                    refine ⟨238671969977705576712373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272917173214429742465989 238671969977705576712373)
                    ·
                      rfl

theorem cell22_697218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_697218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697218 prefixEnd_697218 := by exact prefixLift 697218
  have htrace : WordTrace (prefixWord ++ tailWord_697218) baseStart_697218 baseEnd_697218 := by
    simpa [prefixWord, tailWord_697218, baseEnd_697218] using wordTrace_append hprefix tailTrace_697218
  have hstable : (prefixWord ++ tailWord_697218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697218).length < 2 ^ (prefixWord ++ tailWord_697218).sum := by decide
  have hdescent : baseEnd_697218 < baseStart_697218 := by decide
  rcases family_descends (prefixWord ++ tailWord_697218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697261 : List Nat := [1, 5, 2, 3, 2, 1, 2, 6]
def baseStart_697261 : Nat := 118140960795 + 697261 * 2 ^ 59
def prefixEnd_697261 : Nat := 4983230072969 + 3 ^ 40 * 697261 * 2
def baseEnd_697261 : Nat := 26520743306274199765249

theorem tailTrace_697261 : CollatzResearch.WordTrace tailWord_697261 prefixEnd_697261 26520743306274199765249 := by
  unfold tailWord_697261
  simp only [CollatzResearch.WordTrace]
  refine ⟨25431197926949954543251637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16954131951299969695501091 25431197926949954543251637)
  ·
    refine ⟨2384174805651558238429841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25431197926949954543251637 2384174805651558238429841)
    ·
      refine ⟨1788131104238668678822381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384174805651558238429841 1788131104238668678822381)
      ·
        refine ⟨670549164089500754558393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1788131104238668678822381 670549164089500754558393)
        ·
          refine ⟨502911873067125565918795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 670549164089500754558393 502911873067125565918795)
          ·
            refine ⟨754367809600688348878193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502911873067125565918795 754367809600688348878193)
            ·
              refine ⟨565775857200516261658645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754367809600688348878193 565775857200516261658645)
              ·
                refine ⟨26520743306274199765249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 565775857200516261658645 26520743306274199765249)
                ·
                  rfl

theorem cell22_697261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 6].length) (baseStart_697261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697261 prefixEnd_697261 := by exact prefixLift 697261
  have htrace : WordTrace (prefixWord ++ tailWord_697261) baseStart_697261 baseEnd_697261 := by
    simpa [prefixWord, tailWord_697261, baseEnd_697261] using wordTrace_append hprefix tailTrace_697261
  have hstable : (prefixWord ++ tailWord_697261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697261).length < 2 ^ (prefixWord ++ tailWord_697261).sum := by decide
  have hdescent : baseEnd_697261 < baseStart_697261 := by decide
  rcases family_descends (prefixWord ++ tailWord_697261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697315 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_697315 : Nat := 118140960795 + 697315 * 2 ^ 59
def prefixEnd_697315 : Nat := 4983230072969 + 3 ^ 40 * 697315 * 2
def baseEnd_697315 : Nat := 238705175060029657037075

theorem tailTrace_697315 : CollatzResearch.WordTrace tailWord_697315 prefixEnd_697315 238705175060029657037075 := by
  unfold tailWord_697315
  simp only [CollatzResearch.WordTrace]
  refine ⟨25433167468754321765717399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16955444979169547843811599 25433167468754321765717399)
  ·
    refine ⟨38149751203131482648576099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25433167468754321765717399 38149751203131482648576099)
    ·
      refine ⟨57224626804697223972864149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38149751203131482648576099 57224626804697223972864149)
      ·
        refine ⟨2682404381470182373728007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57224626804697223972864149 2682404381470182373728007)
        ·
          refine ⟨4023606572205273560592011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682404381470182373728007 4023606572205273560592011)
          ·
            refine ⟨6035409858307910340888017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023606572205273560592011 6035409858307910340888017)
            ·
              refine ⟨4526557393730932755666013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6035409858307910340888017 4526557393730932755666013)
              ·
                refine ⟨1697459022649099783374755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4526557393730932755666013 1697459022649099783374755)
                ·
                  refine ⟨2546188533973649675062133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697459022649099783374755 2546188533973649675062133)
                  ·
                    refine ⟨238705175060029657037075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2546188533973649675062133 238705175060029657037075)
                    ·
                      rfl

theorem cell22_697315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_697315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697315 prefixEnd_697315 := by exact prefixLift 697315
  have htrace : WordTrace (prefixWord ++ tailWord_697315) baseStart_697315 baseEnd_697315 := by
    simpa [prefixWord, tailWord_697315, baseEnd_697315] using wordTrace_append hprefix tailTrace_697315
  have hstable : (prefixWord ++ tailWord_697315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697315).length < 2 ^ (prefixWord ++ tailWord_697315).sum := by decide
  have hdescent : baseEnd_697315 < baseStart_697315 := by decide
  rcases family_descends (prefixWord ++ tailWord_697315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697319 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 1, 4]
def baseStart_697319 : Nat := 118140960795 + 697319 * 2 ^ 59
def prefixEnd_697319 : Nat := 4983230072969 + 3 ^ 40 * 697319 * 2
def baseEnd_697319 : Nat := 238706544341774979937063

theorem tailTrace_697319 : CollatzResearch.WordTrace tailWord_697319 prefixEnd_697319 238706544341774979937063 := by
  unfold tailWord_697319
  simp only [CollatzResearch.WordTrace]
  refine ⟨25433313360739830448863011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16955542240493220299242007 25433313360739830448863011)
  ·
    refine ⟨38149970041109745673294517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25433313360739830448863011 38149970041109745673294517)
    ·
      refine ⟨3576559691354038656871361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38149970041109745673294517 3576559691354038656871361)
      ·
        refine ⟨2682419768515528992653521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3576559691354038656871361 2682419768515528992653521)
        ·
          refine ⟨2011814826386646744490141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2682419768515528992653521 2011814826386646744490141)
          ·
            refine ⟨754430559894992529183803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2011814826386646744490141 754430559894992529183803)
            ·
              refine ⟨1131645839842488793775705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754430559894992529183803 1131645839842488793775705)
              ·
                refine ⟨848734379881866595331779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131645839842488793775705 848734379881866595331779)
                ·
                  refine ⟨1273101569822799892997669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848734379881866595331779 1273101569822799892997669)
                  ·
                    refine ⟨238706544341774979937063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273101569822799892997669 238706544341774979937063)
                    ·
                      rfl

theorem cell22_697319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_697319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697319 prefixEnd_697319 := by exact prefixLift 697319
  have htrace : WordTrace (prefixWord ++ tailWord_697319) baseStart_697319 baseEnd_697319 := by
    simpa [prefixWord, tailWord_697319, baseEnd_697319] using wordTrace_append hprefix tailTrace_697319
  have hstable : (prefixWord ++ tailWord_697319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697319).length < 2 ^ (prefixWord ++ tailWord_697319).sum := by decide
  have hdescent : baseEnd_697319 < baseStart_697319 := by decide
  rcases family_descends (prefixWord ++ tailWord_697319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697377 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_697377 : Nat := 118140960795 + 697377 * 2 ^ 59
def prefixEnd_697377 : Nat := 4983230072969 + 3 ^ 40 * 697377 * 2
def baseEnd_697377 : Nat := 238726398927082161986885

theorem tailTrace_697377 : CollatzResearch.WordTrace tailWord_697377 prefixEnd_697377 238726398927082161986885 := by
  unfold tailWord_697377
  simp only [CollatzResearch.WordTrace]
  refine ⟨25435428794529706354474385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16956952529686470902982923 25435428794529706354474385)
  ·
    refine ⟨19076571595897279765855789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25435428794529706354474385 19076571595897279765855789)
    ·
      refine ⟨7153714348461479912195921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19076571595897279765855789 7153714348461479912195921)
      ·
        refine ⟨5365285761346109934146941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153714348461479912195921 5365285761346109934146941)
        ·
          refine ⟨2011982160504791225305103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5365285761346109934146941 2011982160504791225305103)
          ·
            refine ⟨3017973240757186837957655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011982160504791225305103 3017973240757186837957655)
            ·
              refine ⟨4526959861135780256936483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017973240757186837957655 4526959861135780256936483)
              ·
                refine ⟨6790439791703670385404725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526959861135780256936483 6790439791703670385404725)
                ·
                  refine ⟨636603730472219098631693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6790439791703670385404725 636603730472219098631693)
                  ·
                    refine ⟨238726398927082161986885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636603730472219098631693 238726398927082161986885)
                    ·
                      rfl

theorem cell22_697377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_697377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697377 prefixEnd_697377 := by exact prefixLift 697377
  have htrace : WordTrace (prefixWord ++ tailWord_697377) baseStart_697377 baseEnd_697377 := by
    simpa [prefixWord, tailWord_697377, baseEnd_697377] using wordTrace_append hprefix tailTrace_697377
  have hstable : (prefixWord ++ tailWord_697377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697377).length < 2 ^ (prefixWord ++ tailWord_697377).sum := by decide
  have hdescent : baseEnd_697377 < baseStart_697377 := by decide
  rcases family_descends (prefixWord ++ tailWord_697377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697454 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_697454 : Nat := 118140960795 + 697454 * 2 ^ 59
def prefixEnd_697454 : Nat := 4983230072969 + 3 ^ 40 * 697454 * 2
def baseEnd_697454 : Nat := 238752757600679627811649

theorem tailTrace_697454 : CollatzResearch.WordTrace tailWord_697454 prefixEnd_697454 238752757600679627811649 := by
  unfold tailWord_697454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179779651906343563128427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16958824810167165670018277 3179779651906343563128427)
  ·
    refine ⟨4769669477859515344692641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3179779651906343563128427 4769669477859515344692641)
    ·
      refine ⟨3577252108394636508519481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4769669477859515344692641 3577252108394636508519481)
      ·
        refine ⟨2682939081295977381389611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3577252108394636508519481 2682939081295977381389611)
        ·
          refine ⟨4024408621943966072084417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682939081295977381389611 4024408621943966072084417)
          ·
            refine ⟨3018306466457974554063313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024408621943966072084417 3018306466457974554063313)
            ·
              refine ⟨2263729849843480915547485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018306466457974554063313 2263729849843480915547485)
              ·
                refine ⟨848898693691305343330307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2263729849843480915547485 848898693691305343330307)
                ·
                  refine ⟨1273348040536958014995461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848898693691305343330307 1273348040536958014995461)
                  ·
                    refine ⟨238752757600679627811649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273348040536958014995461 238752757600679627811649)
                    ·
                      rfl

theorem cell22_697454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_697454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697454 prefixEnd_697454 := by exact prefixLift 697454
  have htrace : WordTrace (prefixWord ++ tailWord_697454) baseStart_697454 baseEnd_697454 := by
    simpa [prefixWord, tailWord_697454, baseEnd_697454] using wordTrace_append hprefix tailTrace_697454
  have hstable : (prefixWord ++ tailWord_697454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697454).length < 2 ^ (prefixWord ++ tailWord_697454).sum := by decide
  have hdescent : baseEnd_697454 < baseStart_697454 := by decide
  rcases family_descends (prefixWord ++ tailWord_697454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697482 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_697482 : Nat := 118140960795 + 697482 * 2 ^ 59
def prefixEnd_697482 : Nat := 4983230072969 + 3 ^ 40 * 697482 * 2
def baseEnd_697482 : Nat := 238762342572896888111563

theorem tailTrace_697482 : CollatzResearch.WordTrace tailWord_697482 prefixEnd_697482 238762342572896888111563 := by
  unfold tailWord_697482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359814614787327321761675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16959505639432872858031133 6359814614787327321761675)
  ·
    refine ⟨9539721922180990982642513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359814614787327321761675 9539721922180990982642513)
    ·
      refine ⟨7154791441635743236981885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9539721922180990982642513 7154791441635743236981885)
      ·
        refine ⟨2683046790613403713868207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7154791441635743236981885 2683046790613403713868207)
        ·
          refine ⟨4024570185920105570802311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683046790613403713868207 4024570185920105570802311)
          ·
            refine ⟨6036855278880158356203467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024570185920105570802311 6036855278880158356203467)
            ·
              refine ⟨9055282918320237534305201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036855278880158356203467 9055282918320237534305201)
              ·
                refine ⟨6791462188740178150728901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9055282918320237534305201 6791462188740178150728901)
                ·
                  refine ⟨1273399160388783403261669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6791462188740178150728901 1273399160388783403261669)
                  ·
                    refine ⟨238762342572896888111563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273399160388783403261669 238762342572896888111563)
                    ·
                      rfl

theorem cell22_697482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_697482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697482 prefixEnd_697482 := by exact prefixLift 697482
  have htrace : WordTrace (prefixWord ++ tailWord_697482) baseStart_697482 baseEnd_697482 := by
    simpa [prefixWord, tailWord_697482, baseEnd_697482] using wordTrace_append hprefix tailTrace_697482
  have hstable : (prefixWord ++ tailWord_697482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697482).length < 2 ^ (prefixWord ++ tailWord_697482).sum := by decide
  have hdescent : baseEnd_697482 < baseStart_697482 := by decide
  rcases family_descends (prefixWord ++ tailWord_697482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697587 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 6]
def baseStart_697587 : Nat := 118140960795 + 697587 * 2 ^ 59
def prefixEnd_697587 : Nat := 4983230072969 + 3 ^ 40 * 697587 * 2
def baseEnd_697587 : Nat := 79599428739570538078747

theorem tailTrace_697587 : CollatzResearch.WordTrace tailWord_697587 prefixEnd_697587 79599428739570538078747 := by
  unfold tailWord_697587
  simp only [CollatzResearch.WordTrace]
  refine ⟨25443088123768912219619015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16962058749179274813079343 25443088123768912219619015)
  ·
    refine ⟨38164632185653368329428523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25443088123768912219619015 38164632185653368329428523)
    ·
      refine ⟨57246948278480052494142785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38164632185653368329428523 57246948278480052494142785)
      ·
        refine ⟨42935211208860039370607089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57246948278480052494142785 42935211208860039370607089)
        ·
          refine ⟨32201408406645029527955317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42935211208860039370607089 32201408406645029527955317)
          ·
            refine ⟨3018882038122971518245811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32201408406645029527955317 3018882038122971518245811)
            ·
              refine ⟨4528323057184457277368717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018882038122971518245811 4528323057184457277368717)
              ·
                refine ⟨1698121146444171479013269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4528323057184457277368717 1698121146444171479013269)
                ·
                  refine ⟨79599428739570538078747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1698121146444171479013269 79599428739570538078747)
                  ·
                    rfl

theorem cell22_697587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_697587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697587 prefixEnd_697587 := by exact prefixLift 697587
  have htrace : WordTrace (prefixWord ++ tailWord_697587) baseStart_697587 baseEnd_697587 := by
    simpa [prefixWord, tailWord_697587, baseEnd_697587] using wordTrace_append hprefix tailTrace_697587
  have hstable : (prefixWord ++ tailWord_697587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697587).length < 2 ^ (prefixWord ++ tailWord_697587).sum := by decide
  have hdescent : baseEnd_697587 < baseStart_697587 := by decide
  rcases family_descends (prefixWord ++ tailWord_697587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697604 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 6]
def baseStart_697604 : Nat := 118140960795 + 697604 * 2 ^ 59
def prefixEnd_697604 : Nat := 4983230072969 + 3 ^ 40 * 697604 * 2
def baseEnd_697604 : Nat := 79601368555376412187063

theorem tailTrace_697604 : CollatzResearch.WordTrace tailWord_697604 prefixEnd_697604 79601368555376412187063 := by
  unfold tailWord_697604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721854082353662061493933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16962472109804882748658577 12721854082353662061493933)
  ·
    refine ⟨4770695280882623273060225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12721854082353662061493933 4770695280882623273060225)
    ·
      refine ⟨3578021460661967454795169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4770695280882623273060225 3578021460661967454795169)
      ·
        refine ⟨2683516095496475591096377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3578021460661967454795169 2683516095496475591096377)
        ·
          refine ⟨2012637071622356693322283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2683516095496475591096377 2012637071622356693322283)
          ·
            refine ⟨3018955607433535039983425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012637071622356693322283 3018955607433535039983425)
            ·
              refine ⟨2264216705575151279987569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018955607433535039983425 2264216705575151279987569)
              ·
                refine ⟨1698162529181363459990677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264216705575151279987569 1698162529181363459990677)
                ·
                  refine ⟨79601368555376412187063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1698162529181363459990677 79601368555376412187063)
                  ·
                    rfl

theorem cell22_697604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_697604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697604 prefixEnd_697604 := by exact prefixLift 697604
  have htrace : WordTrace (prefixWord ++ tailWord_697604) baseStart_697604 baseEnd_697604 := by
    simpa [prefixWord, tailWord_697604, baseEnd_697604] using wordTrace_append hprefix tailTrace_697604
  have hstable : (prefixWord ++ tailWord_697604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697604).length < 2 ^ (prefixWord ++ tailWord_697604).sum := by decide
  have hdescent : baseEnd_697604 < baseStart_697604 := by decide
  rcases family_descends (prefixWord ++ tailWord_697604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697617 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_697617 : Nat := 118140960795 + 697617 * 2 ^ 59
def prefixEnd_697617 : Nat := 4983230072969 + 3 ^ 40 * 697617 * 2
def baseEnd_697617 : Nat := 238808555831801535986149

theorem tailTrace_697617 : CollatzResearch.WordTrace tailWord_697617 prefixEnd_697617 238808555831801535986149 := by
  unfold tailWord_697617
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444182313660227343211105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16962788209106818228807403 25444182313660227343211105)
  ·
    refine ⟨19083136735245170507408329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25444182313660227343211105 19083136735245170507408329)
    ·
      refine ⟨14312352551433877880556247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19083136735245170507408329 14312352551433877880556247)
      ·
        refine ⟨21468528827150816820834371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14312352551433877880556247 21468528827150816820834371)
        ·
          refine ⟨32202793240726225231251557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21468528827150816820834371 32202793240726225231251557)
          ·
            refine ⟨6038023732636167230859667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32202793240726225231251557 6038023732636167230859667)
            ·
              refine ⟨9057035598954250846289501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038023732636167230859667 9057035598954250846289501)
              ·
                refine ⟨3396388349607844067358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9057035598954250846289501 3396388349607844067358563)
                ·
                  refine ⟨5094582524411766101037845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396388349607844067358563 5094582524411766101037845)
                  ·
                    refine ⟨238808555831801535986149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5094582524411766101037845 238808555831801535986149)
                    ·
                      rfl

theorem cell22_697617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_697617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697617 prefixEnd_697617 := by exact prefixLift 697617
  have htrace : WordTrace (prefixWord ++ tailWord_697617) baseStart_697617 baseEnd_697617 := by
    simpa [prefixWord, tailWord_697617, baseEnd_697617] using wordTrace_append hprefix tailTrace_697617
  have hstable : (prefixWord ++ tailWord_697617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697617).length < 2 ^ (prefixWord ++ tailWord_697617).sum := by decide
  have hdescent : baseEnd_697617 < baseStart_697617 := by decide
  rcases family_descends (prefixWord ++ tailWord_697617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697636 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_697636 : Nat := 118140960795 + 697636 * 2 ^ 59
def prefixEnd_697636 : Nat := 4983230072969 + 3 ^ 40 * 697636 * 2
def baseEnd_697636 : Nat := 238815059920091819761091

theorem tailTrace_697636 : CollatzResearch.WordTrace tailWord_697636 prefixEnd_697636 238815059920091819761091 := by
  unfold tailWord_697636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722437650295696794076381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16963250200394262392101841 12722437650295696794076381)
  ·
    refine ⟨4770914118860886297778643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12722437650295696794076381 4770914118860886297778643)
    ·
      refine ⟨7156371178291329446667965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770914118860886297778643 7156371178291329446667965)
      ·
        refine ⟨2683639191859248542500487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7156371178291329446667965 2683639191859248542500487)
        ·
          refine ⟨4025458787788872813750731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683639191859248542500487 4025458787788872813750731)
          ·
            refine ⟨6038188181683309220626097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025458787788872813750731 6038188181683309220626097)
            ·
              refine ⟨4528641136262481915469573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038188181683309220626097 4528641136262481915469573)
              ·
                refine ⟨849120213049215359150545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4528641136262481915469573 849120213049215359150545)
                ·
                  refine ⟨636840159786911519362909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849120213049215359150545 636840159786911519362909)
                  ·
                    refine ⟨238815059920091819761091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636840159786911519362909 238815059920091819761091)
                    ·
                      rfl

theorem cell22_697636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_697636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697636 prefixEnd_697636 := by exact prefixLift 697636
  have htrace : WordTrace (prefixWord ++ tailWord_697636) baseStart_697636 baseEnd_697636 := by
    simpa [prefixWord, tailWord_697636, baseEnd_697636] using wordTrace_append hprefix tailTrace_697636
  have hstable : (prefixWord ++ tailWord_697636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697636).length < 2 ^ (prefixWord ++ tailWord_697636).sum := by decide
  have hdescent : baseEnd_697636 < baseStart_697636 := by decide
  rcases family_descends (prefixWord ++ tailWord_697636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697649 : List Nat := [1, 2, 2, 3, 3, 2, 2, 7]
def baseStart_697649 : Nat := 118140960795 + 697649 * 2 ^ 59
def prefixEnd_697649 : Nat := 4983230072969 + 3 ^ 40 * 697649 * 2
def baseEnd_697649 : Nat := 26535501120640457687339

theorem tailTrace_697649 : CollatzResearch.WordTrace tailWord_697649 prefixEnd_697649 26535501120640457687339 := by
  unfold tailWord_697649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445349449544296808376001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16963566299696197872250667 25445349449544296808376001)
  ·
    refine ⟨19084012087158222606282001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25445349449544296808376001 19084012087158222606282001)
    ·
      refine ⟨14313009065368666954711501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19084012087158222606282001 14313009065368666954711501)
      ·
        refine ⟨5367378399513250108016813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14313009065368666954711501 5367378399513250108016813)
        ·
          refine ⟨2012766899817468790506305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5367378399513250108016813 2012766899817468790506305)
          ·
            refine ⟨1509575174863101592879729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2012766899817468790506305 1509575174863101592879729)
            ·
              refine ⟨1132181381147326194659797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509575174863101592879729 1132181381147326194659797)
              ·
                refine ⟨26535501120640457687339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1132181381147326194659797 26535501120640457687339)
                ·
                  rfl

theorem cell22_697649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 7].length) (baseStart_697649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697649 prefixEnd_697649 := by exact prefixLift 697649
  have htrace : WordTrace (prefixWord ++ tailWord_697649) baseStart_697649 baseEnd_697649 := by
    simpa [prefixWord, tailWord_697649, baseEnd_697649] using wordTrace_append hprefix tailTrace_697649
  have hstable : (prefixWord ++ tailWord_697649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697649).length < 2 ^ (prefixWord ++ tailWord_697649).sum := by decide
  have hdescent : baseEnd_697649 < baseStart_697649 := by decide
  rcases family_descends (prefixWord ++ tailWord_697649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697653 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_697653 : Nat := 118140960795 + 697653 * 2 ^ 59
def prefixEnd_697653 : Nat := 4983230072969 + 3 ^ 40 * 697653 * 2
def baseEnd_697653 : Nat := 238820879367509442086039

theorem tailTrace_697653 : CollatzResearch.WordTrace tailWord_697653 prefixEnd_697653 238820879367509442086039 := by
  unfold tailWord_697653
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445495341529805491521613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16963663561019870327681075 25445495341529805491521613)
  ·
    refine ⟨9542060753073677059320605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25445495341529805491521613 9542060753073677059320605)
    ·
      refine ⟨3578272782402628897245227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9542060753073677059320605 3578272782402628897245227)
      ·
        refine ⟨5367409173603943345867841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578272782402628897245227 5367409173603943345867841)
        ·
          refine ⟨4025556880202957509400881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5367409173603943345867841 4025556880202957509400881)
          ·
            refine ⟨3019167660152218132050661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025556880202957509400881 3019167660152218132050661)
            ·
              refine ⟨566093936278540899759499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3019167660152218132050661 566093936278540899759499)
              ·
                refine ⟨849140904417811349639249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566093936278540899759499 849140904417811349639249)
                ·
                  refine ⟨636855678313358512229437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849140904417811349639249 636855678313358512229437)
                  ·
                    refine ⟨238820879367509442086039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636855678313358512229437 238820879367509442086039)
                    ·
                      rfl

theorem cell22_697653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_697653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697653 prefixEnd_697653 := by exact prefixLift 697653
  have htrace : WordTrace (prefixWord ++ tailWord_697653) baseStart_697653 baseEnd_697653 := by
    simpa [prefixWord, tailWord_697653, baseEnd_697653] using wordTrace_append hprefix tailTrace_697653
  have hstable : (prefixWord ++ tailWord_697653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697653).length < 2 ^ (prefixWord ++ tailWord_697653).sum := by decide
  have hdescent : baseEnd_697653 < baseStart_697653 := by decide
  rcases family_descends (prefixWord ++ tailWord_697653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697664 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_697664 : Nat := 118140960795 + 697664 * 2 ^ 59
def prefixEnd_697664 : Nat := 4983230072969 + 3 ^ 40 * 697664 * 2
def baseEnd_697664 : Nat := 238824644892309080061005

theorem tailTrace_697664 : CollatzResearch.WordTrace tailWord_697664 prefixEnd_697664 238824644892309080061005 := by
  unfold tailWord_697664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722948272244977185086023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16963931029659969580114697 12722948272244977185086023)
  ·
    refine ⟨19084422408367465777629035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722948272244977185086023 19084422408367465777629035)
    ·
      refine ⟨28626633612551198666443553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19084422408367465777629035 28626633612551198666443553)
      ·
        refine ⟨21469975209413398999832665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28626633612551198666443553 21469975209413398999832665)
        ·
          refine ⟨16102481407060049249874499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21469975209413398999832665 16102481407060049249874499)
          ·
            refine ⟨24153722110590073874811749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16102481407060049249874499 24153722110590073874811749)
            ·
              refine ⟨4528822895735638851527203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24153722110590073874811749 4528822895735638851527203)
              ·
                refine ⟨6793234343603458277290805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528822895735638851527203 6793234343603458277290805)
                ·
                  refine ⟨636865719712824213496013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6793234343603458277290805 636865719712824213496013)
                  ·
                    refine ⟨238824644892309080061005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 636865719712824213496013 238824644892309080061005)
                    ·
                      rfl

theorem cell22_697664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_697664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697664 prefixEnd_697664 := by exact prefixLift 697664
  have htrace : WordTrace (prefixWord ++ tailWord_697664) baseStart_697664 baseEnd_697664 := by
    simpa [prefixWord, tailWord_697664, baseEnd_697664] using wordTrace_append hprefix tailTrace_697664
  have hstable : (prefixWord ++ tailWord_697664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697664).length < 2 ^ (prefixWord ++ tailWord_697664).sum := by decide
  have hdescent : baseEnd_697664 < baseStart_697664 := by decide
  rcases family_descends (prefixWord ++ tailWord_697664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697668 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_697668 : Nat := 118140960795 + 697668 * 2 ^ 59
def prefixEnd_697668 : Nat := 4983230072969 + 3 ^ 40 * 697668 * 2
def baseEnd_697668 : Nat := 238826014174054402960993

theorem tailTrace_697668 : CollatzResearch.WordTrace tailWord_697668 prefixEnd_697668 238826014174054402960993 := by
  unfold tailWord_697668
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723021218237731526658829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16964028290983642035545105 12723021218237731526658829)
  ·
    refine ⟨4771132956839149322497061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12723021218237731526658829 4771132956839149322497061)
    ·
      refine ⟨894587429407340497968199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4771132956839149322497061 894587429407340497968199)
      ·
        refine ⟨1341881144111010746952299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894587429407340497968199 1341881144111010746952299)
        ·
          refine ⟨2012821716166516120428449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341881144111010746952299 2012821716166516120428449)
          ·
            refine ⟨1509616287124887090321337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2012821716166516120428449 1509616287124887090321337)
            ·
              refine ⟨1132212215343665317741003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509616287124887090321337 1132212215343665317741003)
              ·
                refine ⟨1698318323015497976611505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132212215343665317741003 1698318323015497976611505)
                ·
                  refine ⟨1273738742261623482458629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698318323015497976611505 1273738742261623482458629)
                  ·
                    refine ⟨238826014174054402960993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273738742261623482458629 238826014174054402960993)
                    ·
                      rfl

theorem cell22_697668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_697668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697668 prefixEnd_697668 := by exact prefixLift 697668
  have htrace : WordTrace (prefixWord ++ tailWord_697668) baseStart_697668 baseEnd_697668 := by
    simpa [prefixWord, tailWord_697668, baseEnd_697668] using wordTrace_append hprefix tailTrace_697668
  have hstable : (prefixWord ++ tailWord_697668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697668).length < 2 ^ (prefixWord ++ tailWord_697668).sum := by decide
  have hdescent : baseEnd_697668 < baseStart_697668 := by decide
  rcases family_descends (prefixWord ++ tailWord_697668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697670 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_697670 : Nat := 118140960795 + 697670 * 2 ^ 59
def prefixEnd_697670 : Nat := 4983230072969 + 3 ^ 40 * 697670 * 2
def baseEnd_697670 : Nat := 238826698814927064410987

theorem tailTrace_697670 : CollatzResearch.WordTrace tailWord_697670 prefixEnd_697670 238826698814927064410987 := by
  unfold tailWord_697670
  simp only [CollatzResearch.WordTrace]
  refine ⟨795191105702131793590327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16964076921645478263260309 795191105702131793590327)
  ·
    refine ⟨1192786658553197690385491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 795191105702131793590327 1192786658553197690385491)
    ·
      refine ⟨1789179987829796535578237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192786658553197690385491 1789179987829796535578237)
      ·
        refine ⟨670942495436173700841839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1789179987829796535578237 670942495436173700841839)
        ·
          refine ⟨1006413743154260551262759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670942495436173700841839 1006413743154260551262759)
          ·
            refine ⟨1509620614731390826894139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006413743154260551262759 1509620614731390826894139)
            ·
              refine ⟨2264430922097086240341209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509620614731390826894139 2264430922097086240341209)
              ·
                refine ⟨1698323191572814680255907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264430922097086240341209 1698323191572814680255907)
                ·
                  refine ⟨2547484787359222020383861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698323191572814680255907 2547484787359222020383861)
                  ·
                    refine ⟨238826698814927064410987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2547484787359222020383861 238826698814927064410987)
                    ·
                      rfl

theorem cell22_697670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_697670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697670 prefixEnd_697670 := by exact prefixLift 697670
  have htrace : WordTrace (prefixWord ++ tailWord_697670) baseStart_697670 baseEnd_697670 := by
    simpa [prefixWord, tailWord_697670, baseEnd_697670] using wordTrace_append hprefix tailTrace_697670
  have hstable : (prefixWord ++ tailWord_697670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697670).length < 2 ^ (prefixWord ++ tailWord_697670).sum := by decide
  have hdescent : baseEnd_697670 < baseStart_697670 := by decide
  rcases family_descends (prefixWord ++ tailWord_697670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697707 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_697707 : Nat := 118140960795 + 697707 * 2 ^ 59
def prefixEnd_697707 : Nat := 4983230072969 + 3 ^ 40 * 697707 * 2
def baseEnd_697707 : Nat := 238839364671071301235873

theorem tailTrace_697707 : CollatzResearch.WordTrace tailWord_697707 prefixEnd_697707 238839364671071301235873 := by
  unfold tailWord_697707
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447464883334172713987375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16964976588889448475991583 25447464883334172713987375)
  ·
    refine ⟨38171197325001259070981063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25447464883334172713987375 38171197325001259070981063)
    ·
      refine ⟨57256795987501888606471595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38171197325001259070981063 57256795987501888606471595)
      ·
        refine ⟨85885193981252832909707393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57256795987501888606471595 85885193981252832909707393)
        ·
          refine ⟨64413895485939624682280545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85885193981252832909707393 64413895485939624682280545)
          ·
            refine ⟨48310421614454718511710409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64413895485939624682280545 48310421614454718511710409)
            ·
              refine ⟨36232816210841038883782807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48310421614454718511710409 36232816210841038883782807)
              ·
                refine ⟨54349224316261558325674211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36232816210841038883782807 54349224316261558325674211)
                ·
                  refine ⟨81523836474392337488511317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54349224316261558325674211 81523836474392337488511317)
                  ·
                    refine ⟨238839364671071301235873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 81523836474392337488511317 238839364671071301235873)
                    ·
                      rfl

theorem cell22_697707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_697707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697707 prefixEnd_697707 := by exact prefixLift 697707
  have htrace : WordTrace (prefixWord ++ tailWord_697707) baseStart_697707 baseEnd_697707 := by
    simpa [prefixWord, tailWord_697707, baseEnd_697707] using wordTrace_append hprefix tailTrace_697707
  have hstable : (prefixWord ++ tailWord_697707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697707).length < 2 ^ (prefixWord ++ tailWord_697707).sum := by decide
  have hdescent : baseEnd_697707 < baseStart_697707 := by decide
  rcases family_descends (prefixWord ++ tailWord_697707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697709 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_697709 : Nat := 118140960795 + 697709 * 2 ^ 59
def prefixEnd_697709 : Nat := 4983230072969 + 3 ^ 40 * 697709 * 2
def baseEnd_697709 : Nat := 238840049311943962685867

theorem tailTrace_697709 : CollatzResearch.WordTrace tailWord_697709 prefixEnd_697709 238840049311943962685867 := by
  unfold tailWord_697709
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447537829326927055560181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16965025219551284703706787 25447537829326927055560181)
  ·
    refine ⟨2385706671499399411458767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25447537829326927055560181 2385706671499399411458767)
    ·
      refine ⟨3578560007249099117188151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385706671499399411458767 3578560007249099117188151)
      ·
        refine ⟨5367840010873648675782227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578560007249099117188151 5367840010873648675782227)
        ·
          refine ⟨8051760016310473013673341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367840010873648675782227 8051760016310473013673341)
          ·
            refine ⟨3019410006116427380127503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8051760016310473013673341 3019410006116427380127503)
            ·
              refine ⟨4529115009174641070191255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019410006116427380127503 4529115009174641070191255)
              ·
                refine ⟨6793672513761961605286883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4529115009174641070191255 6793672513761961605286883)
                ·
                  refine ⟨10190508770642942407930325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6793672513761961605286883 10190508770642942407930325)
                  ·
                    refine ⟨238840049311943962685867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10190508770642942407930325 238840049311943962685867)
                    ·
                      rfl

theorem cell22_697709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_697709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697709 prefixEnd_697709 := by exact prefixLift 697709
  have htrace : WordTrace (prefixWord ++ tailWord_697709) baseStart_697709 baseEnd_697709 := by
    simpa [prefixWord, tailWord_697709, baseEnd_697709] using wordTrace_append hprefix tailTrace_697709
  have hstable : (prefixWord ++ tailWord_697709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697709).length < 2 ^ (prefixWord ++ tailWord_697709).sum := by decide
  have hdescent : baseEnd_697709 < baseStart_697709 := by decide
  rcases family_descends (prefixWord ++ tailWord_697709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697724 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_697724 : Nat := 118140960795 + 697724 * 2 ^ 59
def prefixEnd_697724 : Nat := 4983230072969 + 3 ^ 40 * 697724 * 2
def baseEnd_697724 : Nat := 238845184118488923560821

theorem tailTrace_697724 : CollatzResearch.WordTrace tailWord_697724 prefixEnd_697724 238845184118488923560821 := by
  unfold tailWord_697724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724042462136292308678113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16965389949515056411570817 12724042462136292308678113)
  ·
    refine ⟨9543031846602219231508585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12724042462136292308678113 9543031846602219231508585)
    ·
      refine ⟨7157273884951664423631439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9543031846602219231508585 7157273884951664423631439)
      ·
        refine ⟨10735910827427496635447159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157273884951664423631439 10735910827427496635447159)
        ·
          refine ⟨16103866241141244953170739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735910827427496635447159 16103866241141244953170739)
          ·
            refine ⟨24155799361711867429756109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16103866241141244953170739 24155799361711867429756109)
            ·
              refine ⟨9058424760641950286158541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24155799361711867429756109 9058424760641950286158541)
              ·
                refine ⟨3396909285240731357309453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9058424760641950286158541 3396909285240731357309453)
                ·
                  refine ⟨1273840981965274258991045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3396909285240731357309453 1273840981965274258991045)
                  ·
                    refine ⟨238845184118488923560821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273840981965274258991045 238845184118488923560821)
                    ·
                      rfl

theorem cell22_697724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_697724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697724 prefixEnd_697724 := by exact prefixLift 697724
  have htrace : WordTrace (prefixWord ++ tailWord_697724) baseStart_697724 baseEnd_697724 := by
    simpa [prefixWord, tailWord_697724, baseEnd_697724] using wordTrace_append hprefix tailTrace_697724
  have hstable : (prefixWord ++ tailWord_697724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697724).length < 2 ^ (prefixWord ++ tailWord_697724).sum := by decide
  have hdescent : baseEnd_697724 < baseStart_697724 := by decide
  rcases family_descends (prefixWord ++ tailWord_697724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697863 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 5]
def baseStart_697863 : Nat := 118140960795 + 697863 * 2 ^ 59
def prefixEnd_697863 : Nat := 4983230072969 + 3 ^ 40 * 697863 * 2
def baseEnd_697863 : Nat := 79630922219712964778465

theorem tailTrace_697863 : CollatzResearch.WordTrace tailWord_697863 prefixEnd_697863 79630922219712964778465 := by
  unfold tailWord_697863
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453154670769011356666243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16968769780512674237777495 25453154670769011356666243)
  ·
    refine ⟨38179732006153517034999365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25453154670769011356666243 38179732006153517034999365)
    ·
      refine ⟨7158699751153784444062381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38179732006153517034999365 7158699751153784444062381)
      ·
        refine ⟨2684512406682669166523393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7158699751153784444062381 2684512406682669166523393)
        ·
          refine ⟨2013384305012001874892545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2684512406682669166523393 2013384305012001874892545)
          ·
            refine ⟨1510038228759001406169409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2013384305012001874892545 1510038228759001406169409)
            ·
              refine ⟨1132528671569251054627057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510038228759001406169409 1132528671569251054627057)
              ·
                refine ⟨849396503676938290970293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132528671569251054627057 849396503676938290970293)
                ·
                  refine ⟨79630922219712964778465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 849396503676938290970293 79630922219712964778465)
                  ·
                    rfl

theorem cell22_697863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 5].length) (baseStart_697863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697863 prefixEnd_697863 := by exact prefixLift 697863
  have htrace : WordTrace (prefixWord ++ tailWord_697863) baseStart_697863 baseEnd_697863 := by
    simpa [prefixWord, tailWord_697863, baseEnd_697863] using wordTrace_append hprefix tailTrace_697863
  have hstable : (prefixWord ++ tailWord_697863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697863).length < 2 ^ (prefixWord ++ tailWord_697863).sum := by decide
  have hdescent : baseEnd_697863 < baseStart_697863 := by decide
  rcases family_descends (prefixWord ++ tailWord_697863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697985 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_697985 : Nat := 118140960795 + 697985 * 2 ^ 59
def prefixEnd_697985 : Nat := 4983230072969 + 3 ^ 40 * 697985 * 2
def baseEnd_697985 : Nat := 238934529752371242785021

theorem tailTrace_697985 : CollatzResearch.WordTrace tailWord_697985 prefixEnd_697985 238934529752371242785021 := by
  unfold tailWord_697985
  simp only [CollatzResearch.WordTrace]
  refine ⟨25457604376327026192607409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16971736250884684128404939 25457604376327026192607409)
  ·
    refine ⟨19093203282245269644455557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25457604376327026192607409 19093203282245269644455557)
    ·
      refine ⟨3579975615420988058335417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19093203282245269644455557 3579975615420988058335417)
      ·
        refine ⟨2684981711565741043751563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3579975615420988058335417 2684981711565741043751563)
        ·
          refine ⟨4027472567348611565627345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684981711565741043751563 4027472567348611565627345)
          ·
            refine ⟨3020604425511458674220509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027472567348611565627345 3020604425511458674220509)
            ·
              refine ⟨1132726659566797002832691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3020604425511458674220509 1132726659566797002832691)
              ·
                refine ⟨1699089989350195504249037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132726659566797002832691 1699089989350195504249037)
                ·
                  refine ⟨637158746006323314093389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1699089989350195504249037 637158746006323314093389)
                  ·
                    refine ⟨238934529752371242785021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637158746006323314093389 238934529752371242785021)
                    ·
                      rfl

theorem cell22_697985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_697985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697985 prefixEnd_697985 := by exact prefixLift 697985
  have htrace : WordTrace (prefixWord ++ tailWord_697985) baseStart_697985 baseEnd_697985 := by
    simpa [prefixWord, tailWord_697985, baseEnd_697985] using wordTrace_append hprefix tailTrace_697985
  have hstable : (prefixWord ++ tailWord_697985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697985).length < 2 ^ (prefixWord ++ tailWord_697985).sum := by decide
  have hdescent : baseEnd_697985 < baseStart_697985 := by decide
  rcases family_descends (prefixWord ++ tailWord_697985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697996 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_697996 : Nat := 118140960795 + 697996 * 2 ^ 59
def prefixEnd_697996 : Nat := 4983230072969 + 3 ^ 40 * 697996 * 2
def baseEnd_697996 : Nat := 238938295277170880759987

theorem tailTrace_697996 : CollatzResearch.WordTrace tailWord_697996 prefixEnd_697996 238938295277170880759987 := by
  unfold tailWord_697996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729002789643587535628921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16972003719524783380838561 12729002789643587535628921)
  ·
    refine ⟨9546752092232690651721691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12729002789643587535628921 9546752092232690651721691)
    ·
      refine ⟨14320128138349035977582537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9546752092232690651721691 14320128138349035977582537)
      ·
        refine ⟨10740096103761776983186903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14320128138349035977582537 10740096103761776983186903)
        ·
          refine ⟨16110144155642665474780355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10740096103761776983186903 16110144155642665474780355)
          ·
            refine ⟨24165216233463998212170533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16110144155642665474780355 24165216233463998212170533)
            ·
              refine ⟨4530978043774499664781975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24165216233463998212170533 4530978043774499664781975)
              ·
                refine ⟨6796467065661749497172963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530978043774499664781975 6796467065661749497172963)
                ·
                  refine ⟨10194700598492624245759445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6796467065661749497172963 10194700598492624245759445)
                  ·
                    refine ⟨238938295277170880759987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10194700598492624245759445 238938295277170880759987)
                    ·
                      rfl

theorem cell22_697996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_697996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_697996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_697996 prefixEnd_697996 := by exact prefixLift 697996
  have htrace : WordTrace (prefixWord ++ tailWord_697996) baseStart_697996 baseEnd_697996 := by
    simpa [prefixWord, tailWord_697996, baseEnd_697996] using wordTrace_append hprefix tailTrace_697996
  have hstable : (prefixWord ++ tailWord_697996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697996).length < 2 ^ (prefixWord ++ tailWord_697996).sum := by decide
  have hdescent : baseEnd_697996 < baseStart_697996 := by decide
  rcases family_descends (prefixWord ++ tailWord_697996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698060 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 6]
def baseStart_698060 : Nat := 118140960795 + 698060 * 2 ^ 59
def prefixEnd_698060 : Nat := 4983230072969 + 3 ^ 40 * 698060 * 2
def baseEnd_698060 : Nat := 79653401261698682386597

theorem tailTrace_698060 : CollatzResearch.WordTrace tailWord_698060 prefixEnd_698060 79653401261698682386597 := by
  unfold tailWord_698060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730169925527657000793817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16973559900703542667725089 12730169925527657000793817)
  ·
    refine ⟨9547627444145742750595363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12730169925527657000793817 9547627444145742750595363)
    ·
      refine ⟨14321441166218614125893045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9547627444145742750595363 14321441166218614125893045)
      ·
        refine ⟨1342635109332995074302473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14321441166218614125893045 1342635109332995074302473)
        ·
          refine ⟨1006976331999746305726855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342635109332995074302473 1006976331999746305726855)
          ·
            refine ⟨1510464497999619458590283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006976331999746305726855 1510464497999619458590283)
            ·
              refine ⟨2265696746999429187885425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510464497999619458590283 2265696746999429187885425)
              ·
                refine ⟨1699272560249571890914069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265696746999429187885425 1699272560249571890914069)
                ·
                  refine ⟨79653401261698682386597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1699272560249571890914069 79653401261698682386597)
                  ·
                    rfl

theorem cell22_698060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_698060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698060 prefixEnd_698060 := by exact prefixLift 698060
  have htrace : WordTrace (prefixWord ++ tailWord_698060) baseStart_698060 baseEnd_698060 := by
    simpa [prefixWord, tailWord_698060, baseEnd_698060] using wordTrace_append hprefix tailTrace_698060
  have hstable : (prefixWord ++ tailWord_698060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698060).length < 2 ^ (prefixWord ++ tailWord_698060).sum := by decide
  have hdescent : baseEnd_698060 < baseStart_698060 := by decide
  rcases family_descends (prefixWord ++ tailWord_698060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698073 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_698073 : Nat := 118140960795 + 698073 * 2 ^ 59
def prefixEnd_698073 : Nat := 4983230072969 + 3 ^ 40 * 698073 * 2
def baseEnd_698073 : Nat := 238964653950768346584751

theorem tailTrace_698073 : CollatzResearch.WordTrace tailWord_698073 prefixEnd_698073 238964653950768346584751 := by
  unfold tailWord_698073
  simp only [CollatzResearch.WordTrace]
  refine ⟨25460814000008217221810873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16973876000005478147873915 25460814000008217221810873)
  ·
    refine ⟨19095610500006162916358155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25460814000008217221810873 19095610500006162916358155)
    ·
      refine ⟨28643415750009244374537233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19095610500006162916358155 28643415750009244374537233)
      ·
        refine ⟨21482561812506933280902925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28643415750009244374537233 21482561812506933280902925)
        ·
          refine ⟨8055960679690099980338597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21482561812506933280902925 8055960679690099980338597)
          ·
            refine ⟨1510492627441893746313487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8055960679690099980338597 1510492627441893746313487)
            ·
              refine ⟨2265738941162840619470231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510492627441893746313487 2265738941162840619470231)
              ·
                refine ⟨3398608411744260929205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265738941162840619470231 3398608411744260929205347)
                ·
                  refine ⟨5097912617616391393808021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398608411744260929205347 5097912617616391393808021)
                  ·
                    refine ⟨238964653950768346584751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5097912617616391393808021 238964653950768346584751)
                    ·
                      rfl

theorem cell22_698073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_698073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698073 prefixEnd_698073 := by exact prefixLift 698073
  have htrace : WordTrace (prefixWord ++ tailWord_698073) baseStart_698073 baseEnd_698073 := by
    simpa [prefixWord, tailWord_698073, baseEnd_698073] using wordTrace_append hprefix tailTrace_698073
  have hstable : (prefixWord ++ tailWord_698073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698073).length < 2 ^ (prefixWord ++ tailWord_698073).sum := by decide
  have hdescent : baseEnd_698073 < baseStart_698073 := by decide
  rcases family_descends (prefixWord ++ tailWord_698073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698088 : List Nat := [2, 1, 4, 1, 3, 2, 9]
def baseStart_698088 : Nat := 118140960795 + 698088 * 2 ^ 59
def prefixEnd_698088 : Nat := 4983230072969 + 3 ^ 40 * 698088 * 2
def baseEnd_698088 : Nat := 8850732916937529905915

theorem tailTrace_698088 : CollatzResearch.WordTrace tailWord_698088 prefixEnd_698088 8850732916937529905915 := by
  unfold tailWord_698088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730680547476937391803459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16974240729969249855737945 12730680547476937391803459)
  ·
    refine ⟨19096020821215406087705189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12730680547476937391803459 19096020821215406087705189)
    ·
      refine ⟨3580503903977888641444723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19096020821215406087705189 3580503903977888641444723)
      ·
        refine ⟨5370755855966832962167085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580503903977888641444723 5370755855966832962167085)
        ·
          refine ⟨2014033445987562360812657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5370755855966832962167085 2014033445987562360812657)
          ·
            refine ⟨1510525084490671770609493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2014033445987562360812657 1510525084490671770609493)
            ·
              refine ⟨8850732916937529905915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1510525084490671770609493 8850732916937529905915)
              ·
                rfl

theorem cell22_698088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 9].length) (baseStart_698088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698088 prefixEnd_698088 := by exact prefixLift 698088
  have htrace : WordTrace (prefixWord ++ tailWord_698088) baseStart_698088 baseEnd_698088 := by
    simpa [prefixWord, tailWord_698088, baseEnd_698088] using wordTrace_append hprefix tailTrace_698088
  have hstable : (prefixWord ++ tailWord_698088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698088).length < 2 ^ (prefixWord ++ tailWord_698088).sum := by decide
  have hdescent : baseEnd_698088 < baseStart_698088 := by decide
  rcases family_descends (prefixWord ++ tailWord_698088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698120 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_698120 : Nat := 118140960795 + 698120 * 2 ^ 59
def prefixEnd_698120 : Nat := 4983230072969 + 3 ^ 40 * 698120 * 2
def baseEnd_698120 : Nat := 238980743011275890659607

theorem tailTrace_698120 : CollatzResearch.WordTrace tailWord_698120 prefixEnd_698120 238980743011275890659607 := by
  unfold tailWord_698120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731264115418972124385907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16975018820558629499181209 12731264115418972124385907)
  ·
    refine ⟨19096896173128458186578861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12731264115418972124385907 19096896173128458186578861)
    ·
      refine ⟨7161336064923171819967073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19096896173128458186578861 7161336064923171819967073)
      ·
        refine ⟨5371002048692378864975305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7161336064923171819967073 5371002048692378864975305)
        ·
          refine ⟨4028251536519284148731479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5371002048692378864975305 4028251536519284148731479)
          ·
            refine ⟨6042377304778926223097219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028251536519284148731479 6042377304778926223097219)
            ·
              refine ⟨9063565957168389334645829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042377304778926223097219 9063565957168389334645829)
              ·
                refine ⟨1699418616969073000246093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9063565957168389334645829 1699418616969073000246093)
                ·
                  refine ⟨637281981363402375092285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1699418616969073000246093 637281981363402375092285)
                  ·
                    refine ⟨238980743011275890659607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637281981363402375092285 238980743011275890659607)
                    ·
                      rfl

theorem cell22_698120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_698120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698120 prefixEnd_698120 := by exact prefixLift 698120
  have htrace : WordTrace (prefixWord ++ tailWord_698120) baseStart_698120 baseEnd_698120 := by
    simpa [prefixWord, tailWord_698120, baseEnd_698120] using wordTrace_append hprefix tailTrace_698120
  have hstable : (prefixWord ++ tailWord_698120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698120).length < 2 ^ (prefixWord ++ tailWord_698120).sum := by decide
  have hdescent : baseEnd_698120 < baseStart_698120 := by decide
  rcases family_descends (prefixWord ++ tailWord_698120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698133 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 7]
def baseStart_698133 : Nat := 118140960795 + 698133 * 2 ^ 59
def prefixEnd_698133 : Nat := 4983230072969 + 3 ^ 40 * 698133 * 2
def baseEnd_698133 : Nat := 79661731058982730028189

theorem tailTrace_698133 : CollatzResearch.WordTrace tailWord_698133 prefixEnd_698133 79661731058982730028189 := by
  unfold tailWord_698133
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463002379790847468995053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16975334919860564979330035 25463002379790847468995053)
  ·
    refine ⟨9548625892421567800873145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25463002379790847468995053 9548625892421567800873145)
    ·
      refine ⟨7161469419316175850654859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9548625892421567800873145 7161469419316175850654859)
      ·
        refine ⟨10742204128974263775982289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7161469419316175850654859 10742204128974263775982289)
        ·
          refine ⟨8056653096730697831986717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10742204128974263775982289 8056653096730697831986717)
          ·
            refine ⟨3021244911274011686995019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8056653096730697831986717 3021244911274011686995019)
            ·
              refine ⟨4531867366911017530492529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021244911274011686995019 4531867366911017530492529)
              ·
                refine ⟨3398900525183263147869397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531867366911017530492529 3398900525183263147869397)
                ·
                  refine ⟨79661731058982730028189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3398900525183263147869397 79661731058982730028189)
                  ·
                    rfl

theorem cell22_698133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_698133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698133 prefixEnd_698133 := by exact prefixLift 698133
  have htrace : WordTrace (prefixWord ++ tailWord_698133) baseStart_698133 baseEnd_698133 := by
    simpa [prefixWord, tailWord_698133, baseEnd_698133] using wordTrace_append hprefix tailTrace_698133
  have hstable : (prefixWord ++ tailWord_698133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698133).length < 2 ^ (prefixWord ++ tailWord_698133).sum := by decide
  have hdescent : baseEnd_698133 < baseStart_698133 := by decide
  rcases family_descends (prefixWord ++ tailWord_698133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698240 : List Nat := [2, 1, 1, 2, 1, 2, 7, 6]
def baseStart_698240 : Nat := 118140960795 + 698240 * 2 ^ 59
def prefixEnd_698240 : Nat := 4983230072969 + 3 ^ 40 * 698240 * 2
def baseEnd_698240 : Nat := 26557980162626175295471

theorem tailTrace_698240 : CollatzResearch.WordTrace tailWord_698240 prefixEnd_698240 26557980162626175295471 := by
  unfold tailWord_698240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733452495201602371570087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16977936660268803162093449 12733452495201602371570087)
  ·
    refine ⟨19100178742802403557355131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12733452495201602371570087 19100178742802403557355131)
    ·
      refine ⟨28650268114203605336032697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19100178742802403557355131 28650268114203605336032697)
      ·
        refine ⟨21487701085652704002024523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28650268114203605336032697 21487701085652704002024523)
        ·
          refine ⟨32231551628479056003036785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21487701085652704002024523 32231551628479056003036785)
          ·
            refine ⟨24173663721359292002277589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32231551628479056003036785 24173663721359292002277589)
            ·
              refine ⟨566570243469358406303381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24173663721359292002277589 566570243469358406303381)
              ·
                refine ⟨26557980162626175295471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 566570243469358406303381 26557980162626175295471)
                ·
                  rfl

theorem cell22_698240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 6].length) (baseStart_698240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698240 prefixEnd_698240 := by exact prefixLift 698240
  have htrace : WordTrace (prefixWord ++ tailWord_698240) baseStart_698240 baseEnd_698240 := by
    simpa [prefixWord, tailWord_698240, baseEnd_698240] using wordTrace_append hprefix tailTrace_698240
  have hstable : (prefixWord ++ tailWord_698240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698240).length < 2 ^ (prefixWord ++ tailWord_698240).sum := by decide
  have hdescent : baseEnd_698240 < baseStart_698240 := by decide
  rcases family_descends (prefixWord ++ tailWord_698240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698360 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_698360 : Nat := 118140960795 + 698360 * 2 ^ 59
def prefixEnd_698360 : Nat := 4983230072969 + 3 ^ 40 * 698360 * 2
def baseEnd_698360 : Nat := 239062899915995264658871

theorem tailTrace_698360 : CollatzResearch.WordTrace tailWord_698360 prefixEnd_698360 239062899915995264658871 := by
  unfold tailWord_698360
  simp only [CollatzResearch.WordTrace]
  refine ⟨12735640874984232618754267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16980854499978976825005689 12735640874984232618754267)
  ·
    refine ⟨19103461312476348928131401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12735640874984232618754267 19103461312476348928131401)
    ·
      refine ⟨14327595984357261696098551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19103461312476348928131401 14327595984357261696098551)
      ·
        refine ⟨21491393976535892544147827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327595984357261696098551 21491393976535892544147827)
        ·
          refine ⟨32237090964803838816221741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21491393976535892544147827 32237090964803838816221741)
          ·
            refine ⟨12088909111801439556083153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32237090964803838816221741 12088909111801439556083153)
            ·
              refine ⟨9066681833851079667062365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12088909111801439556083153 9066681833851079667062365)
              ·
                refine ⟨3400005687694154875148387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9066681833851079667062365 3400005687694154875148387)
                ·
                  refine ⟨5100008531541232312722581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400005687694154875148387 5100008531541232312722581)
                  ·
                    refine ⟨239062899915995264658871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5100008531541232312722581 239062899915995264658871)
                    ·
                      rfl

theorem cell22_698360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_698360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698360 prefixEnd_698360 := by exact prefixLift 698360
  have htrace : WordTrace (prefixWord ++ tailWord_698360) baseStart_698360 baseEnd_698360 := by
    simpa [prefixWord, tailWord_698360, baseEnd_698360] using wordTrace_append hprefix tailTrace_698360
  have hstable : (prefixWord ++ tailWord_698360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698360).length < 2 ^ (prefixWord ++ tailWord_698360).sum := by decide
  have hdescent : baseEnd_698360 < baseStart_698360 := by decide
  rcases family_descends (prefixWord ++ tailWord_698360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698375 : List Nat := [1, 1, 4, 3, 1, 12]
def baseStart_698375 : Nat := 118140960795 + 698375 * 2 ^ 59
def prefixEnd_698375 : Nat := 4983230072969 + 3 ^ 40 * 698375 * 2
def baseEnd_698375 : Nat := 2951457218796792907825

theorem tailTrace_698375 : CollatzResearch.WordTrace tailWord_698375 prefixEnd_698375 2951457218796792907825 := by
  unfold tailWord_698375
  simp only [CollatzResearch.WordTrace]
  refine ⟨25471828844914122799304579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16981219229942748532869719 25471828844914122799304579)
  ·
    refine ⟨38207743267371184198956869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25471828844914122799304579 38207743267371184198956869)
    ·
      refine ⟨7163951862632097037304413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38207743267371184198956869 7163951862632097037304413)
      ·
        refine ⟨2686481948487036388989155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7163951862632097037304413 2686481948487036388989155)
        ·
          refine ⟨4029722922730554583483733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686481948487036388989155 4029722922730554583483733)
          ·
            refine ⟨2951457218796792907825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4029722922730554583483733 2951457218796792907825)
            ·
              rfl

theorem cell22_698375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 12].length) (baseStart_698375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698375 prefixEnd_698375 := by exact prefixLift 698375
  have htrace : WordTrace (prefixWord ++ tailWord_698375) baseStart_698375 baseEnd_698375 := by
    simpa [prefixWord, tailWord_698375, baseEnd_698375] using wordTrace_append hprefix tailTrace_698375
  have hstable : (prefixWord ++ tailWord_698375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698375).length < 2 ^ (prefixWord ++ tailWord_698375).sum := by decide
  have hdescent : baseEnd_698375 < baseStart_698375 := by decide
  rcases family_descends (prefixWord ++ tailWord_698375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698379 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 2, 3]
def baseStart_698379 : Nat := 118140960795 + 698379 * 2 ^ 59
def prefixEnd_698379 : Nat := 4983230072969 + 3 ^ 40 * 698379 * 2
def baseEnd_698379 : Nat := 239069404004285548433813

theorem tailTrace_698379 : CollatzResearch.WordTrace tailWord_698379 prefixEnd_698379 239069404004285548433813 := by
  unfold tailWord_698379
  simp only [CollatzResearch.WordTrace]
  refine ⟨25471974736899631482450191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16981316491266420988300127 25471974736899631482450191)
  ·
    refine ⟨38207962105349447223675287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25471974736899631482450191 38207962105349447223675287)
    ·
      refine ⟨57311943158024170835512931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38207962105349447223675287 57311943158024170835512931)
      ·
        refine ⟨85967914737036256253269397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57311943158024170835512931 85967914737036256253269397)
        ·
          refine ⟨4029746003298574511872003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85967914737036256253269397 4029746003298574511872003)
          ·
            refine ⟨6044619004947861767808005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029746003298574511872003 6044619004947861767808005)
            ·
              refine ⟨1133366063427724081464001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6044619004947861767808005 1133366063427724081464001)
              ·
                refine ⟨850024547570793061098001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133366063427724081464001 850024547570793061098001)
                ·
                  refine ⟨637518410678094795823501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850024547570793061098001 637518410678094795823501)
                  ·
                    refine ⟨239069404004285548433813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637518410678094795823501 239069404004285548433813)
                    ·
                      rfl

theorem cell22_698379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3].length) (baseStart_698379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698379 prefixEnd_698379 := by exact prefixLift 698379
  have htrace : WordTrace (prefixWord ++ tailWord_698379) baseStart_698379 baseEnd_698379 := by
    simpa [prefixWord, tailWord_698379, baseEnd_698379] using wordTrace_append hprefix tailTrace_698379
  have hstable : (prefixWord ++ tailWord_698379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698379).length < 2 ^ (prefixWord ++ tailWord_698379).sum := by decide
  have hdescent : baseEnd_698379 < baseStart_698379 := by decide
  rcases family_descends (prefixWord ++ tailWord_698379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698430 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_698430 : Nat := 118140960795 + 698430 * 2 ^ 59
def prefixEnd_698430 : Nat := 4983230072969 + 3 ^ 40 * 698430 * 2
def baseEnd_698430 : Nat := 239086862346538415408657

theorem tailTrace_698430 : CollatzResearch.WordTrace tailWord_698430 prefixEnd_698430 239086862346538415408657 := by
  unfold tailWord_698430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184229357464358399069593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16982556573143244795037829 3184229357464358399069593)
  ·
    refine ⟨2388172018098268799302195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3184229357464358399069593 2388172018098268799302195)
    ·
      refine ⟨3582258027147403198953293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388172018098268799302195 3582258027147403198953293)
      ·
        refine ⟨1343346760180276199607485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3582258027147403198953293 1343346760180276199607485)
        ·
          refine ⟨503755035067603574852807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1343346760180276199607485 503755035067603574852807)
          ·
            refine ⟨755632552601405362279211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503755035067603574852807 755632552601405362279211)
            ·
              refine ⟨1133448828902108043418817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755632552601405362279211 1133448828902108043418817)
              ·
                refine ⟨850086621676581032564113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133448828902108043418817 850086621676581032564113)
                ·
                  refine ⟨637564966257435774423085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850086621676581032564113 637564966257435774423085)
                  ·
                    refine ⟨239086862346538415408657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637564966257435774423085 239086862346538415408657)
                    ·
                      rfl

theorem cell22_698430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_698430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698430 prefixEnd_698430 := by exact prefixLift 698430
  have htrace : WordTrace (prefixWord ++ tailWord_698430) baseStart_698430 baseEnd_698430 := by
    simpa [prefixWord, tailWord_698430, baseEnd_698430] using wordTrace_append hprefix tailTrace_698430
  have hstable : (prefixWord ++ tailWord_698430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698430).length < 2 ^ (prefixWord ++ tailWord_698430).sum := by decide
  have hdescent : baseEnd_698430 < baseStart_698430 := by decide
  rcases family_descends (prefixWord ++ tailWord_698430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698467 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_698467 : Nat := 118140960795 + 698467 * 2 ^ 59
def prefixEnd_698467 : Nat := 4983230072969 + 3 ^ 40 * 698467 * 2
def baseEnd_698467 : Nat := 239099528202682652233543

theorem tailTrace_698467 : CollatzResearch.WordTrace tailWord_698467 prefixEnd_698467 239099528202682652233543 := by
  unfold tailWord_698467
  simp only [CollatzResearch.WordTrace]
  refine ⟨25475184360580822511653655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16983456240387215007769103 25475184360580822511653655)
  ·
    refine ⟨38212776540871233767480483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25475184360580822511653655 38212776540871233767480483)
    ·
      refine ⟨57319164811306850651220725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38212776540871233767480483 57319164811306850651220725)
      ·
        refine ⟨5373671701060017248551943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57319164811306850651220725 5373671701060017248551943)
        ·
          refine ⟨8060507551590025872827915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373671701060017248551943 8060507551590025872827915)
          ·
            refine ⟨12090761327385038809241873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060507551590025872827915 12090761327385038809241873)
            ·
              refine ⟨9068070995538779106931405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12090761327385038809241873 9068070995538779106931405)
              ·
                refine ⟨3400526623327042165099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9068070995538779106931405 3400526623327042165099277)
                ·
                  refine ⟨1275197483747640811912229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3400526623327042165099277 1275197483747640811912229)
                  ·
                    refine ⟨239099528202682652233543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275197483747640811912229 239099528202682652233543)
                    ·
                      rfl

theorem cell22_698467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_698467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698467 prefixEnd_698467 := by exact prefixLift 698467
  have htrace : WordTrace (prefixWord ++ tailWord_698467) baseStart_698467 baseEnd_698467 := by
    simpa [prefixWord, tailWord_698467, baseEnd_698467] using wordTrace_append hprefix tailTrace_698467
  have hstable : (prefixWord ++ tailWord_698467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698467).length < 2 ^ (prefixWord ++ tailWord_698467).sum := by decide
  have hdescent : baseEnd_698467 < baseStart_698467 := by decide
  rcases family_descends (prefixWord ++ tailWord_698467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698499 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 6]
def baseStart_698499 : Nat := 118140960795 + 698499 * 2 ^ 59
def prefixEnd_698499 : Nat := 4983230072969 + 3 ^ 40 * 698499 * 2
def baseEnd_698499 : Nat := 79703494152215078477815

theorem tailTrace_698499 : CollatzResearch.WordTrace tailWord_698499 prefixEnd_698499 79703494152215078477815 := by
  unfold tailWord_698499
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476351496464891976818551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16984234330976594651212367 25476351496464891976818551)
  ·
    refine ⟨38214527244697337965227827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25476351496464891976818551 38214527244697337965227827)
    ·
      refine ⟨57321790867046006947841741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38214527244697337965227827 57321790867046006947841741)
      ·
        refine ⟨21495671575142252605440653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57321790867046006947841741 21495671575142252605440653)
        ·
          refine ⟨8060876840678344727040245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21495671575142252605440653 8060876840678344727040245)
          ·
            refine ⟨755707203813594818160023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8060876840678344727040245 755707203813594818160023)
            ·
              refine ⟨1133560805720392227240035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755707203813594818160023 1133560805720392227240035)
              ·
                refine ⟨1700341208580588340860053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133560805720392227240035 1700341208580588340860053)
                ·
                  refine ⟨79703494152215078477815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1700341208580588340860053 79703494152215078477815)
                  ·
                    rfl

theorem cell22_698499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 6].length) (baseStart_698499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698499 prefixEnd_698499 := by exact prefixLift 698499
  have htrace : WordTrace (prefixWord ++ tailWord_698499) baseStart_698499 baseEnd_698499 := by
    simpa [prefixWord, tailWord_698499, baseEnd_698499] using wordTrace_append hprefix tailTrace_698499
  have hstable : (prefixWord ++ tailWord_698499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698499).length < 2 ^ (prefixWord ++ tailWord_698499).sum := by decide
  have hdescent : baseEnd_698499 < baseStart_698499 := by decide
  rcases family_descends (prefixWord ++ tailWord_698499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698512 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_698512 : Nat := 118140960795 + 698512 * 2 ^ 59
def prefixEnd_698512 : Nat := 4983230072969 + 3 ^ 40 * 698512 * 2
def baseEnd_698512 : Nat := 239114932622317534858405

theorem tailTrace_698512 : CollatzResearch.WordTrace tailWord_698512 prefixEnd_698512 239114932622317534858405 := by
  unfold tailWord_698512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12738412822708897598520895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16984550430278530131361193 12738412822708897598520895)
  ·
    refine ⟨19107619234063346397781343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12738412822708897598520895 19107619234063346397781343)
    ·
      refine ⟨28661428851095019596672015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19107619234063346397781343 28661428851095019596672015)
      ·
        refine ⟨42992143276642529395008023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28661428851095019596672015 42992143276642529395008023)
        ·
          refine ⟨64488214914963794092512035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42992143276642529395008023 64488214914963794092512035)
          ·
            refine ⟨96732322372445691138768053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64488214914963794092512035 96732322372445691138768053)
            ·
              refine ⟨9068655222416783544259505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96732322372445691138768053 9068655222416783544259505)
              ·
                refine ⟨6801491416812587658194629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9068655222416783544259505 6801491416812587658194629)
                ·
                  refine ⟨1275279640652360185911493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6801491416812587658194629 1275279640652360185911493)
                  ·
                    refine ⟨239114932622317534858405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275279640652360185911493 239114932622317534858405)
                    ·
                      rfl

theorem cell22_698512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_698512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698512 prefixEnd_698512 := by exact prefixLift 698512
  have htrace : WordTrace (prefixWord ++ tailWord_698512) baseStart_698512 baseEnd_698512 := by
    simpa [prefixWord, tailWord_698512, baseEnd_698512] using wordTrace_append hprefix tailTrace_698512
  have hstable : (prefixWord ++ tailWord_698512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698512).length < 2 ^ (prefixWord ++ tailWord_698512).sum := by decide
  have hdescent : baseEnd_698512 < baseStart_698512 := by decide
  rcases family_descends (prefixWord ++ tailWord_698512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698514 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_698514 : Nat := 118140960795 + 698514 * 2 ^ 59
def prefixEnd_698514 : Nat := 4983230072969 + 3 ^ 40 * 698514 * 2
def baseEnd_698514 : Nat := 239115617263190196308399

theorem tailTrace_698514 : CollatzResearch.WordTrace tailWord_698514 prefixEnd_698514 239115617263190196308399 := by
  unfold tailWord_698514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369224647852637384653649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16984599060940366359076397 6369224647852637384653649)
  ·
    refine ⟨4776918485889478038490237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6369224647852637384653649 4776918485889478038490237)
    ·
      refine ⟨1791344432208554264433839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4776918485889478038490237 1791344432208554264433839)
      ·
        refine ⟨2687016648312831396650759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791344432208554264433839 2687016648312831396650759)
        ·
          refine ⟨4030524972469247094976139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687016648312831396650759 4030524972469247094976139)
          ·
            refine ⟨6045787458703870642464209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030524972469247094976139 6045787458703870642464209)
            ·
              refine ⟨4534340594027902981848157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6045787458703870642464209 4534340594027902981848157)
              ·
                refine ⟨1700377722760463618193059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534340594027902981848157 1700377722760463618193059)
                ·
                  refine ⟨2550566584140695427289589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700377722760463618193059 2550566584140695427289589)
                  ·
                    refine ⟨239115617263190196308399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2550566584140695427289589 239115617263190196308399)
                    ·
                      rfl

theorem cell22_698514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_698514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698514 prefixEnd_698514 := by exact prefixLift 698514
  have htrace : WordTrace (prefixWord ++ tailWord_698514) baseStart_698514 baseEnd_698514 := by
    simpa [prefixWord, tailWord_698514, baseEnd_698514] using wordTrace_append hprefix tailTrace_698514
  have hstable : (prefixWord ++ tailWord_698514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698514).length < 2 ^ (prefixWord ++ tailWord_698514).sum := by decide
  have hdescent : baseEnd_698514 < baseStart_698514 := by decide
  rcases family_descends (prefixWord ++ tailWord_698514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698529 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_698529 : Nat := 118140960795 + 698529 * 2 ^ 59
def prefixEnd_698529 : Nat := 4983230072969 + 3 ^ 40 * 698529 * 2
def baseEnd_698529 : Nat := 239120752069735157183353

theorem tailTrace_698529 : CollatzResearch.WordTrace tailWord_698529 prefixEnd_698529 239120752069735157183353 := by
  unfold tailWord_698529
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477445686356207100410641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16984963790904138066940427 25477445686356207100410641)
  ·
    refine ⟨19108084264767155325307981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25477445686356207100410641 19108084264767155325307981)
    ·
      refine ⟨7165531599287683246990493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19108084264767155325307981 7165531599287683246990493)
      ·
        refine ⟨2687074349732881217621435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7165531599287683246990493 2687074349732881217621435)
        ·
          refine ⟨4030611524599321826432153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687074349732881217621435 4030611524599321826432153)
          ·
            refine ⟨3022958643449491369824115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030611524599321826432153 3022958643449491369824115)
            ·
              refine ⟨4534437965174237054736173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022958643449491369824115 4534437965174237054736173)
              ·
                refine ⟨1700414236940338895526065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4534437965174237054736173 1700414236940338895526065)
                ·
                  refine ⟨1275310677705254171644549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700414236940338895526065 1275310677705254171644549)
                  ·
                    refine ⟨239120752069735157183353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275310677705254171644549 239120752069735157183353)
                    ·
                      rfl

theorem cell22_698529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_698529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698529 prefixEnd_698529 := by exact prefixLift 698529
  have htrace : WordTrace (prefixWord ++ tailWord_698529) baseStart_698529 baseEnd_698529 := by
    simpa [prefixWord, tailWord_698529, baseEnd_698529] using wordTrace_append hprefix tailTrace_698529
  have hstable : (prefixWord ++ tailWord_698529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698529).length < 2 ^ (prefixWord ++ tailWord_698529).sum := by decide
  have hdescent : baseEnd_698529 < baseStart_698529 := by decide
  rcases family_descends (prefixWord ++ tailWord_698529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698559 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 3, 3]
def baseStart_698559 : Nat := 118140960795 + 698559 * 2 ^ 59
def prefixEnd_698559 : Nat := 4983230072969 + 3 ^ 40 * 698559 * 2
def baseEnd_698559 : Nat := 239131021682825078933261

theorem tailTrace_698559 : CollatzResearch.WordTrace tailWord_698559 prefixEnd_698559 239131021682825078933261 := by
  unfold tailWord_698559
  simp only [CollatzResearch.WordTrace]
  refine ⟨25478539876247522224002731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16985693250831681482668487 25478539876247522224002731)
  ·
    refine ⟨38217809814371283336004097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25478539876247522224002731 38217809814371283336004097)
    ·
      refine ⟨28663357360778462502003073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38217809814371283336004097 28663357360778462502003073)
      ·
        refine ⟨21497518020583846876502305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28663357360778462502003073 21497518020583846876502305)
        ·
          refine ⟨16123138515437885157376729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21497518020583846876502305 16123138515437885157376729)
          ·
            refine ⟨12092353886578413868032547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16123138515437885157376729 12092353886578413868032547)
            ·
              refine ⟨18138530829867620802048821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12092353886578413868032547 18138530829867620802048821)
              ·
                refine ⟨1700487265300089450192077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18138530829867620802048821 1700487265300089450192077)
                ·
                  refine ⟨637682724487533543822029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1700487265300089450192077 637682724487533543822029)
                  ·
                    refine ⟨239131021682825078933261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637682724487533543822029 239131021682825078933261)
                    ·
                      rfl

theorem cell22_698559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_698559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698559 prefixEnd_698559 := by exact prefixLift 698559
  have htrace : WordTrace (prefixWord ++ tailWord_698559) baseStart_698559 baseEnd_698559 := by
    simpa [prefixWord, tailWord_698559, baseEnd_698559] using wordTrace_append hprefix tailTrace_698559
  have hstable : (prefixWord ++ tailWord_698559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698559).length < 2 ^ (prefixWord ++ tailWord_698559).sum := by decide
  have hdescent : baseEnd_698559 < baseStart_698559 := by decide
  rcases family_descends (prefixWord ++ tailWord_698559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_698587 : Nat := 118140960795 + 698587 * 2 ^ 59
def prefixEnd_698587 : Nat := 4983230072969 + 3 ^ 40 * 698587 * 2
def baseEnd_698587 : Nat := 239140606655042339233175

theorem tailTrace_698587 : CollatzResearch.WordTrace tailWord_698587 prefixEnd_698587 239140606655042339233175 := by
  unfold tailWord_698587
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479561120146083006022015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16986374080097388670681343 25479561120146083006022015)
  ·
    refine ⟨38219341680219124509033023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25479561120146083006022015 38219341680219124509033023)
    ·
      refine ⟨57329012520328686763549535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38219341680219124509033023 57329012520328686763549535)
      ·
        refine ⟨85993518780493030145324303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57329012520328686763549535 85993518780493030145324303)
        ·
          refine ⟨128990278170739545217986455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85993518780493030145324303 128990278170739545217986455)
          ·
            refine ⟨193485417256109317826979683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128990278170739545217986455 193485417256109317826979683)
            ·
              refine ⟨290228125884163976740469525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193485417256109317826979683 290228125884163976740469525)
              ·
                refine ⟨13604443400820186409709509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290228125884163976740469525 13604443400820186409709509)
                ·
                  refine ⟨2550833137653784951820533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13604443400820186409709509 2550833137653784951820533)
                  ·
                    refine ⟨239140606655042339233175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2550833137653784951820533 239140606655042339233175)
                    ·
                      rfl

theorem cell22_698587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_698587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698587 prefixEnd_698587 := by exact prefixLift 698587
  have htrace : WordTrace (prefixWord ++ tailWord_698587) baseStart_698587 baseEnd_698587 := by
    simpa [prefixWord, tailWord_698587, baseEnd_698587] using wordTrace_append hprefix tailTrace_698587
  have hstable : (prefixWord ++ tailWord_698587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698587).length < 2 ^ (prefixWord ++ tailWord_698587).sum := by decide
  have hdescent : baseEnd_698587 < baseStart_698587 := by decide
  rcases family_descends (prefixWord ++ tailWord_698587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698593 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 1, 3]
def baseStart_698593 : Nat := 118140960795 + 698593 * 2 ^ 59
def prefixEnd_698593 : Nat := 4983230072969 + 3 ^ 40 * 698593 * 2
def baseEnd_698593 : Nat := 239142660577660323583157

theorem tailTrace_698593 : CollatzResearch.WordTrace tailWord_698593 prefixEnd_698593 239142660577660323583157 := by
  unfold tailWord_698593
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479779958124346030740433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16986519972082897353826955 25479779958124346030740433)
  ·
    refine ⟨19109834968593259523055325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25479779958124346030740433 19109834968593259523055325)
    ·
      refine ⟨7166188113222472321145747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19109834968593259523055325 7166188113222472321145747)
      ·
        refine ⟨10749282169833708481718621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7166188113222472321145747 10749282169833708481718621)
        ·
          refine ⟨4030980813687640680644483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10749282169833708481718621 4030980813687640680644483)
          ·
            refine ⟨6046471220531461020966725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030980813687640680644483 6046471220531461020966725)
            ·
              refine ⟨1133713353849648941431261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6046471220531461020966725 1133713353849648941431261)
              ·
                refine ⟨425142507693618353036723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133713353849648941431261 425142507693618353036723)
                ·
                  refine ⟨637713761540427529555085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425142507693618353036723 637713761540427529555085)
                  ·
                    refine ⟨239142660577660323583157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637713761540427529555085 239142660577660323583157)
                    ·
                      rfl

theorem cell22_698593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_698593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698593 prefixEnd_698593 := by exact prefixLift 698593
  have htrace : WordTrace (prefixWord ++ tailWord_698593) baseStart_698593 baseEnd_698593 := by
    simpa [prefixWord, tailWord_698593, baseEnd_698593] using wordTrace_append hprefix tailTrace_698593
  have hstable : (prefixWord ++ tailWord_698593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698593).length < 2 ^ (prefixWord ++ tailWord_698593).sum := by decide
  have hdescent : baseEnd_698593 < baseStart_698593 := by decide
  rcases family_descends (prefixWord ++ tailWord_698593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698634 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_698634 : Nat := 118140960795 + 698634 * 2 ^ 59
def prefixEnd_698634 : Nat := 4983230072969 + 3 ^ 40 * 698634 * 2
def baseEnd_698634 : Nat := 79718898571849961102677

theorem tailTrace_698634 : CollatzResearch.WordTrace tailWord_698634 prefixEnd_698634 79718898571849961102677 := by
  unfold tailWord_698634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370318837743952508245739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16987516900650540021988637 6370318837743952508245739)
  ·
    refine ⟨9555478256615928762368609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370318837743952508245739 9555478256615928762368609)
    ·
      refine ⟨7166608692461946571776457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9555478256615928762368609 7166608692461946571776457)
      ·
        refine ⟨5374956519346459928832343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7166608692461946571776457 5374956519346459928832343)
        ·
          refine ⟨8062434779019689893248515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374956519346459928832343 8062434779019689893248515)
          ·
            refine ⟨12093652168529534839872773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062434779019689893248515 12093652168529534839872773)
            ·
              refine ⟨2267559781599287782476145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12093652168529534839872773 2267559781599287782476145)
              ·
                refine ⟨1700669836199465836857109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267559781599287782476145 1700669836199465836857109)
                ·
                  refine ⟨79718898571849961102677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1700669836199465836857109 79718898571849961102677)
                  ·
                    rfl

theorem cell22_698634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_698634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698634 prefixEnd_698634 := by exact prefixLift 698634
  have htrace : WordTrace (prefixWord ++ tailWord_698634) baseStart_698634 baseEnd_698634 := by
    simpa [prefixWord, tailWord_698634, baseEnd_698634] using wordTrace_append hprefix tailTrace_698634
  have hstable : (prefixWord ++ tailWord_698634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698634).length < 2 ^ (prefixWord ++ tailWord_698634).sum := by decide
  have hdescent : baseEnd_698634 < baseStart_698634 := by decide
  rcases family_descends (prefixWord ++ tailWord_698634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698636 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_698636 : Nat := 118140960795 + 698636 * 2 ^ 59
def prefixEnd_698636 : Nat := 4983230072969 + 3 ^ 40 * 698636 * 2
def baseEnd_698636 : Nat := 239157380356422544758025

theorem tailTrace_698636 : CollatzResearch.WordTrace tailWord_698636 prefixEnd_698636 239157380356422544758025 := by
  unfold tailWord_698636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740674148484282187277881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16987565531312376249703841 12740674148484282187277881)
  ·
    refine ⟨9555505611363211640458411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12740674148484282187277881 9555505611363211640458411)
    ·
      refine ⟨14333258417044817460687617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555505611363211640458411 14333258417044817460687617)
      ·
        refine ⟨10749943812783613095515713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14333258417044817460687617 10749943812783613095515713)
        ·
          refine ⟨8062457859587709821636785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10749943812783613095515713 8062457859587709821636785)
          ·
            refine ⟨6046843394690782366227589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8062457859587709821636785 6046843394690782366227589)
            ·
              refine ⟨1133783136504521693667673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6046843394690782366227589 1133783136504521693667673)
              ·
                refine ⟨850337352378391270250755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133783136504521693667673 850337352378391270250755)
                ·
                  refine ⟨1275506028567586905376133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850337352378391270250755 1275506028567586905376133)
                  ·
                    refine ⟨239157380356422544758025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275506028567586905376133 239157380356422544758025)
                    ·
                      rfl

theorem cell22_698636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_698636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698636 prefixEnd_698636 := by exact prefixLift 698636
  have htrace : WordTrace (prefixWord ++ tailWord_698636) baseStart_698636 baseEnd_698636 := by
    simpa [prefixWord, tailWord_698636, baseEnd_698636] using wordTrace_append hprefix tailTrace_698636
  have hstable : (prefixWord ++ tailWord_698636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698636).length < 2 ^ (prefixWord ++ tailWord_698636).sum := by decide
  have hdescent : baseEnd_698636 < baseStart_698636 := by decide
  rcases family_descends (prefixWord ++ tailWord_698636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698651 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 4]
def baseStart_698651 : Nat := 118140960795 + 698651 * 2 ^ 59
def prefixEnd_698651 : Nat := 4983230072969 + 3 ^ 40 * 698651 * 2
def baseEnd_698651 : Nat := 79720838387655835210993

theorem tailTrace_698651 : CollatzResearch.WordTrace tailWord_698651 prefixEnd_698651 79720838387655835210993 := by
  unfold tailWord_698651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25481895391914221936351807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16987930261276147957567871 25481895391914221936351807)
  ·
    refine ⟨38222843087871332904527711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25481895391914221936351807 38222843087871332904527711)
    ·
      refine ⟨57334264631806999356791567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38222843087871332904527711 57334264631806999356791567)
      ·
        refine ⟨86001396947710499035187351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57334264631806999356791567 86001396947710499035187351)
        ·
          refine ⟨129002095421565748552781027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86001396947710499035187351 129002095421565748552781027)
          ·
            refine ⟨193503143132348622829171541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129002095421565748552781027 193503143132348622829171541)
            ·
              refine ⟨1133807479291105211889677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 193503143132348622829171541 1133807479291105211889677)
              ·
                refine ⟨425177804734164454458629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133807479291105211889677 425177804734164454458629)
                ·
                  refine ⟨79720838387655835210993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425177804734164454458629 79720838387655835210993)
                  ·
                    rfl

theorem cell22_698651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 4].length) (baseStart_698651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698651 prefixEnd_698651 := by exact prefixLift 698651
  have htrace : WordTrace (prefixWord ++ tailWord_698651) baseStart_698651 baseEnd_698651 := by
    simpa [prefixWord, tailWord_698651, baseEnd_698651] using wordTrace_append hprefix tailTrace_698651
  have hstable : (prefixWord ++ tailWord_698651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698651).length < 2 ^ (prefixWord ++ tailWord_698651).sum := by decide
  have hdescent : baseEnd_698651 < baseStart_698651 := by decide
  rcases family_descends (prefixWord ++ tailWord_698651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_698739 : Nat := 118140960795 + 698739 * 2 ^ 59
def prefixEnd_698739 : Nat := 4983230072969 + 3 ^ 40 * 698739 * 2
def baseEnd_698739 : Nat := 239192639361364609432709

theorem tailTrace_698739 : CollatzResearch.WordTrace tailWord_698739 prefixEnd_698739 239192639361364609432709 := by
  unfold tailWord_698739
  simp only [CollatzResearch.WordTrace]
  refine ⟨25485105015595412965555271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16990070010396941977036847 25485105015595412965555271)
  ·
    refine ⟨38227657523393119448332907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25485105015595412965555271 38227657523393119448332907)
    ·
      refine ⟨57341486285089679172499361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38227657523393119448332907 57341486285089679172499361)
      ·
        refine ⟨43006114713817259379374521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57341486285089679172499361 43006114713817259379374521)
        ·
          refine ⟨32254586035362944534530891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43006114713817259379374521 32254586035362944534530891)
          ·
            refine ⟨48381879053044416801796337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32254586035362944534530891 48381879053044416801796337)
            ·
              refine ⟨36286409289783312601347253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48381879053044416801796337 36286409289783312601347253)
              ·
                refine ⟨3401850870917185556376305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36286409289783312601347253 3401850870917185556376305)
                ·
                  refine ⟨2551388153187889167282229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3401850870917185556376305 2551388153187889167282229)
                  ·
                    refine ⟨239192639361364609432709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2551388153187889167282229 239192639361364609432709)
                    ·
                      rfl

theorem cell22_698739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_698739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698739 prefixEnd_698739 := by exact prefixLift 698739
  have htrace : WordTrace (prefixWord ++ tailWord_698739) baseStart_698739 baseEnd_698739 := by
    simpa [prefixWord, tailWord_698739, baseEnd_698739] using wordTrace_append hprefix tailTrace_698739
  have hstable : (prefixWord ++ tailWord_698739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698739).length < 2 ^ (prefixWord ++ tailWord_698739).sum := by decide
  have hdescent : baseEnd_698739 < baseStart_698739 := by decide
  rcases family_descends (prefixWord ++ tailWord_698739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698805 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_698805 : Nat := 118140960795 + 698805 * 2 ^ 59
def prefixEnd_698805 : Nat := 4983230072969 + 3 ^ 40 * 698805 * 2
def baseEnd_698805 : Nat := 239215232510162437282507

theorem tailTrace_698805 : CollatzResearch.WordTrace tailWord_698805 prefixEnd_698805 239215232510162437282507 := by
  unfold tailWord_698805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25487512233356306237457869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16991674822237537491638579 25487512233356306237457869)
  ·
    refine ⟨9557817087508614839046701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25487512233356306237457869 9557817087508614839046701)
    ·
      refine ⟨3584181407815730564642513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9557817087508614839046701 3584181407815730564642513)
      ·
        refine ⟨2688136055861797923481885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584181407815730564642513 2688136055861797923481885)
        ·
          refine ⟨1008051020948174221305707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2688136055861797923481885 1008051020948174221305707)
          ·
            refine ⟨1512076531422261331958561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008051020948174221305707 1512076531422261331958561)
            ·
              refine ⟨1134057398566695998968921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512076531422261331958561 1134057398566695998968921)
              ·
                refine ⟨850543048925021999226691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134057398566695998968921 850543048925021999226691)
                ·
                  refine ⟨1275814573387532998840037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850543048925021999226691 1275814573387532998840037)
                  ·
                    refine ⟨239215232510162437282507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275814573387532998840037 239215232510162437282507)
                    ·
                      rfl

theorem cell22_698805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_698805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698805 prefixEnd_698805 := by exact prefixLift 698805
  have htrace : WordTrace (prefixWord ++ tailWord_698805) baseStart_698805 baseEnd_698805 := by
    simpa [prefixWord, tailWord_698805, baseEnd_698805] using wordTrace_append hprefix tailTrace_698805
  have hstable : (prefixWord ++ tailWord_698805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698805).length < 2 ^ (prefixWord ++ tailWord_698805).sum := by decide
  have hdescent : baseEnd_698805 < baseStart_698805 := by decide
  rcases family_descends (prefixWord ++ tailWord_698805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698816 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_698816 : Nat := 118140960795 + 698816 * 2 ^ 59
def prefixEnd_698816 : Nat := 4983230072969 + 3 ^ 40 * 698816 * 2
def baseEnd_698816 : Nat := 239218998034962075257473

theorem tailTrace_698816 : CollatzResearch.WordTrace tailWord_698816 prefixEnd_698816 239218998034962075257473 := by
  unfold tailWord_698816
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743956718158227558054151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16991942290877636744072201 12743956718158227558054151)
  ·
    refine ⟨19115935077237341337081227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12743956718158227558054151 19115935077237341337081227)
    ·
      refine ⟨28673902615856012005621841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19115935077237341337081227 28673902615856012005621841)
      ·
        refine ⟨21505426961892009004216381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28673902615856012005621841 21505426961892009004216381)
        ·
          refine ⟨8064535110709503376581143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21505426961892009004216381 8064535110709503376581143)
          ·
            refine ⟨12096802666064255064871715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064535110709503376581143 12096802666064255064871715)
            ·
              refine ⟨18145203999096382597307573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12096802666064255064871715 18145203999096382597307573)
              ·
                refine ⟨1701112874915285868497585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18145203999096382597307573 1701112874915285868497585)
                ·
                  refine ⟨1275834656186464401373189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1701112874915285868497585 1275834656186464401373189)
                  ·
                    refine ⟨239218998034962075257473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275834656186464401373189 239218998034962075257473)
                    ·
                      rfl

theorem cell22_698816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_698816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698816 prefixEnd_698816 := by exact prefixLift 698816
  have htrace : WordTrace (prefixWord ++ tailWord_698816) baseStart_698816 baseEnd_698816 := by
    simpa [prefixWord, tailWord_698816, baseEnd_698816] using wordTrace_append hprefix tailTrace_698816
  have hstable : (prefixWord ++ tailWord_698816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698816).length < 2 ^ (prefixWord ++ tailWord_698816).sum := by decide
  have hdescent : baseEnd_698816 < baseStart_698816 := by decide
  rcases family_descends (prefixWord ++ tailWord_698816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698886 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_698886 : Nat := 118140960795 + 698886 * 2 ^ 59
def prefixEnd_698886 : Nat := 4983230072969 + 3 ^ 40 * 698886 * 2
def baseEnd_698886 : Nat := 239242960465505226007259

theorem tailTrace_698886 : CollatzResearch.WordTrace tailWord_698886 prefixEnd_698886 239242960465505226007259 := by
  unfold tailWord_698886
  simp only [CollatzResearch.WordTrace]
  refine ⟨796577079564464283473641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16993644364041904714104341 796577079564464283473641)
  ·
    refine ⟨597432809673348212605231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 796577079564464283473641 597432809673348212605231)
    ·
      refine ⟨896149214510022318907847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597432809673348212605231 896149214510022318907847)
      ·
        refine ⟨1344223821765033478361771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896149214510022318907847 1344223821765033478361771)
        ·
          refine ⟨2016335732647550217542657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344223821765033478361771 2016335732647550217542657)
          ·
            refine ⟨1512251799485662663156993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016335732647550217542657 1512251799485662663156993)
            ·
              refine ⟨1134188849614246997367745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512251799485662663156993 1134188849614246997367745)
              ·
                refine ⟨850641637210685248025809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134188849614246997367745 850641637210685248025809)
                ·
                  refine ⟨637981227908013936019357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850641637210685248025809 637981227908013936019357)
                  ·
                    refine ⟨239242960465505226007259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637981227908013936019357 239242960465505226007259)
                    ·
                      rfl

theorem cell22_698886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_698886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698886 prefixEnd_698886 := by exact prefixLift 698886
  have htrace : WordTrace (prefixWord ++ tailWord_698886) baseStart_698886 baseEnd_698886 := by
    simpa [prefixWord, tailWord_698886, baseEnd_698886] using wordTrace_append hprefix tailTrace_698886
  have hstable : (prefixWord ++ tailWord_698886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698886).length < 2 ^ (prefixWord ++ tailWord_698886).sum := by decide
  have hdescent : baseEnd_698886 < baseStart_698886 := by decide
  rcases family_descends (prefixWord ++ tailWord_698886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698908 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_698908 : Nat := 118140960795 + 698908 * 2 ^ 59
def prefixEnd_698908 : Nat := 4983230072969 + 3 ^ 40 * 698908 * 2
def baseEnd_698908 : Nat := 239250491515104501957191

theorem tailTrace_698908 : CollatzResearch.WordTrace tailWord_698908 prefixEnd_698908 239250491515104501957191 := by
  unfold tailWord_698908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745634475991577414228689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16994179301322103218971585 12745634475991577414228689)
  ·
    refine ⟨9559225856993683060671517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12745634475991577414228689 9559225856993683060671517)
    ·
      refine ⟨3584709696372631147751819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9559225856993683060671517 3584709696372631147751819)
      ·
        refine ⟨5377064544558946721627729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584709696372631147751819 5377064544558946721627729)
        ·
          refine ⟨4032798408419210041220797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5377064544558946721627729 4032798408419210041220797)
          ·
            refine ⟨1512299403157203765457799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4032798408419210041220797 1512299403157203765457799)
            ·
              refine ⟨2268449104735805648186699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512299403157203765457799 2268449104735805648186699)
              ·
                refine ⟨3402673657103708472280049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268449104735805648186699 3402673657103708472280049)
                ·
                  refine ⟨2552005242827781354210037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402673657103708472280049 2552005242827781354210037)
                  ·
                    refine ⟨239250491515104501957191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2552005242827781354210037 239250491515104501957191)
                    ·
                      rfl

theorem cell22_698908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_698908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698908 prefixEnd_698908 := by exact prefixLift 698908
  have htrace : WordTrace (prefixWord ++ tailWord_698908) baseStart_698908 baseEnd_698908 := by
    simpa [prefixWord, tailWord_698908, baseEnd_698908] using wordTrace_append hprefix tailTrace_698908
  have hstable : (prefixWord ++ tailWord_698908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698908).length < 2 ^ (prefixWord ++ tailWord_698908).sum := by decide
  have hdescent : baseEnd_698908 < baseStart_698908 := by decide
  rcases family_descends (prefixWord ++ tailWord_698908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698940 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_698940 : Nat := 118140960795 + 698940 * 2 ^ 59
def prefixEnd_698940 : Nat := 4983230072969 + 3 ^ 40 * 698940 * 2
def baseEnd_698940 : Nat := 239261445769067085157093

theorem tailTrace_698940 : CollatzResearch.WordTrace tailWord_698940 prefixEnd_698940 239261445769067085157093 := by
  unfold tailWord_698940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12746218043933612146811137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16994957391911482862414849 12746218043933612146811137)
  ·
    refine ⟨9559663532950209110108353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12746218043933612146811137 9559663532950209110108353)
    ·
      refine ⟨7169747649712656832581265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9559663532950209110108353 7169747649712656832581265)
      ·
        refine ⟨5377310737284492624435949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7169747649712656832581265 5377310737284492624435949)
        ·
          refine ⟨2016491526481684734163481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5377310737284492624435949 2016491526481684734163481)
          ·
            refine ⟨1512368644861263550622611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016491526481684734163481 1512368644861263550622611)
            ·
              refine ⟨2268552967291895325933917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512368644861263550622611 2268552967291895325933917)
              ·
                refine ⟨850707362734460747225219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268552967291895325933917 850707362734460747225219)
                ·
                  refine ⟨1276061044101691120837829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850707362734460747225219 1276061044101691120837829)
                  ·
                    refine ⟨239261445769067085157093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276061044101691120837829 239261445769067085157093)
                    ·
                      rfl

theorem cell22_698940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_698940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_698940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_698940 prefixEnd_698940 := by exact prefixLift 698940
  have htrace : WordTrace (prefixWord ++ tailWord_698940) baseStart_698940 baseEnd_698940 := by
    simpa [prefixWord, tailWord_698940, baseEnd_698940] using wordTrace_append hprefix tailTrace_698940
  have hstable : (prefixWord ++ tailWord_698940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698940).length < 2 ^ (prefixWord ++ tailWord_698940).sum := by decide
  have hdescent : baseEnd_698940 < baseStart_698940 := by decide
  rcases family_descends (prefixWord ++ tailWord_698940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699105 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_699105 : Nat := 118140960795 + 699105 * 2 ^ 59
def prefixEnd_699105 : Nat := 4983230072969 + 3 ^ 40 * 699105 * 2
def baseEnd_699105 : Nat := 239317928641061654781587

theorem tailTrace_699105 : CollatzResearch.WordTrace tailWord_699105 prefixEnd_699105 239317928641061654781587 := by
  unfold tailWord_699105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498454132269457473378769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16998969421512971648919179 25498454132269457473378769)
  ·
    refine ⟨19123840599202093105034077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25498454132269457473378769 19123840599202093105034077)
    ·
      refine ⟨7171440224700784914387779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19123840599202093105034077 7171440224700784914387779)
      ·
        refine ⟨10757160337051177371581669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7171440224700784914387779 10757160337051177371581669)
        ·
          refine ⟨2016967563197095757171563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10757160337051177371581669 2016967563197095757171563)
          ·
            refine ⟨3025451344795643635757345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016967563197095757171563 3025451344795643635757345)
            ·
              refine ⟨2269088508596732726818009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025451344795643635757345 2269088508596732726818009)
              ·
                refine ⟨1701816381447549545113507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269088508596732726818009 1701816381447549545113507)
                ·
                  refine ⟨2552724572171324317670261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701816381447549545113507 2552724572171324317670261)
                  ·
                    refine ⟨239317928641061654781587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2552724572171324317670261 239317928641061654781587)
                    ·
                      rfl

theorem cell22_699105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_699105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699105 prefixEnd_699105 := by exact prefixLift 699105
  have htrace : WordTrace (prefixWord ++ tailWord_699105) baseStart_699105 baseEnd_699105 := by
    simpa [prefixWord, tailWord_699105, baseEnd_699105] using wordTrace_append hprefix tailTrace_699105
  have hstable : (prefixWord ++ tailWord_699105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699105).length < 2 ^ (prefixWord ++ tailWord_699105).sum := by decide
  have hdescent : baseEnd_699105 < baseStart_699105 := by decide
  rcases family_descends (prefixWord ++ tailWord_699105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699107 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 4]
def baseStart_699107 : Nat := 118140960795 + 699107 * 2 ^ 59
def prefixEnd_699107 : Nat := 4983230072969 + 3 ^ 40 * 699107 * 2
def baseEnd_699107 : Nat := 79772871093978105410527

theorem tailTrace_699107 : CollatzResearch.WordTrace tailWord_699107 prefixEnd_699107 79772871093978105410527 := by
  unfold tailWord_699107
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498527078262211814951575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16999018052174807876634383 25498527078262211814951575)
  ·
    refine ⟨38247790617393317722427363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25498527078262211814951575 38247790617393317722427363)
    ·
      refine ⟨57371685926089976583641045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38247790617393317722427363 57371685926089976583641045)
      ·
        refine ⟨1344648888892733826179087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57371685926089976583641045 1344648888892733826179087)
        ·
          refine ⟨2016973333339100739268631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344648888892733826179087 2016973333339100739268631)
          ·
            refine ⟨3025460000008651108902947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016973333339100739268631 3025460000008651108902947)
            ·
              refine ⟨4538190000012976663354421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025460000008651108902947 4538190000012976663354421)
              ·
                refine ⟨425455312501216562189477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4538190000012976663354421 425455312501216562189477)
                ·
                  refine ⟨79772871093978105410527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425455312501216562189477 79772871093978105410527)
                  ·
                    rfl

theorem cell22_699107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 4].length) (baseStart_699107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699107 prefixEnd_699107 := by exact prefixLift 699107
  have htrace : WordTrace (prefixWord ++ tailWord_699107) baseStart_699107 baseEnd_699107 := by
    simpa [prefixWord, tailWord_699107, baseEnd_699107] using wordTrace_append hprefix tailTrace_699107
  have hstable : (prefixWord ++ tailWord_699107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699107).length < 2 ^ (prefixWord ++ tailWord_699107).sum := by decide
  have hdescent : baseEnd_699107 < baseStart_699107 := by decide
  rcases family_descends (prefixWord ++ tailWord_699107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699109 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_699109 : Nat := 118140960795 + 699109 * 2 ^ 59
def prefixEnd_699109 : Nat := 4983230072969 + 3 ^ 40 * 699109 * 2
def baseEnd_699109 : Nat := 239319297922806977681575

theorem tailTrace_699109 : CollatzResearch.WordTrace tailWord_699109 prefixEnd_699109 239319297922806977681575 := by
  unfold tailWord_699109
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498600024254966156524381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16999066682836644104349587 25498600024254966156524381)
  ·
    refine ⟨9561975009095612308696643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25498600024254966156524381 9561975009095612308696643)
    ·
      refine ⟨14342962513643418463044965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9561975009095612308696643 14342962513643418463044965)
      ·
        refine ⟨2689305471308140961820931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14342962513643418463044965 2689305471308140961820931)
        ·
          refine ⟨4033958206962211442731397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689305471308140961820931 4033958206962211442731397)
          ·
            refine ⟨756367163805414645512137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4033958206962211442731397 756367163805414645512137)
            ·
              refine ⟨567275372854060984134103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756367163805414645512137 567275372854060984134103)
              ·
                refine ⟨850913059281091476201155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567275372854060984134103 850913059281091476201155)
                ·
                  refine ⟨1276369588921637214301733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850913059281091476201155 1276369588921637214301733)
                  ·
                    refine ⟨239319297922806977681575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276369588921637214301733 239319297922806977681575)
                    ·
                      rfl

theorem cell22_699109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_699109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699109 prefixEnd_699109 := by exact prefixLift 699109
  have htrace : WordTrace (prefixWord ++ tailWord_699109) baseStart_699109 baseEnd_699109 := by
    simpa [prefixWord, tailWord_699109, baseEnd_699109] using wordTrace_append hprefix tailTrace_699109
  have hstable : (prefixWord ++ tailWord_699109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699109).length < 2 ^ (prefixWord ++ tailWord_699109).sum := by decide
  have hdescent : baseEnd_699109 < baseStart_699109 := by decide
  rcases family_descends (prefixWord ++ tailWord_699109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699122 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_699122 : Nat := 118140960795 + 699122 * 2 ^ 59
def prefixEnd_699122 : Nat := 4983230072969 + 3 ^ 40 * 699122 * 2
def baseEnd_699122 : Nat := 239323748088479277106535

theorem tailTrace_699122 : CollatzResearch.WordTrace tailWord_699122 prefixEnd_699122 239323748088479277106535 := by
  unfold tailWord_699122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374768543301967344186905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16999382782138579584498413 6374768543301967344186905)
  ·
    refine ⟨4781076407476475508140179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6374768543301967344186905 4781076407476475508140179)
    ·
      refine ⟨7171614611214713262210269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4781076407476475508140179 7171614611214713262210269)
      ·
        refine ⟨2689355479205517473328851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7171614611214713262210269 2689355479205517473328851)
        ·
          refine ⟨4034033218808276209993277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689355479205517473328851 4034033218808276209993277)
          ·
            refine ⟨1512762457053103578747479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4034033218808276209993277 1512762457053103578747479)
            ·
              refine ⟨2269143685579655368121219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512762457053103578747479 2269143685579655368121219)
              ·
                refine ⟨3403715528369483052181829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269143685579655368121219 3403715528369483052181829)
                ·
                  refine ⟨638196661569278072284093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3403715528369483052181829 638196661569278072284093)
                  ·
                    refine ⟨239323748088479277106535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638196661569278072284093 239323748088479277106535)
                    ·
                      rfl

theorem cell22_699122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_699122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699122 prefixEnd_699122 := by exact prefixLift 699122
  have htrace : WordTrace (prefixWord ++ tailWord_699122) baseStart_699122 baseEnd_699122 := by
    simpa [prefixWord, tailWord_699122, baseEnd_699122] using wordTrace_append hprefix tailTrace_699122
  have hstable : (prefixWord ++ tailWord_699122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699122).length < 2 ^ (prefixWord ++ tailWord_699122).sum := by decide
  have hdescent : baseEnd_699122 < baseStart_699122 := by decide
  rcases family_descends (prefixWord ++ tailWord_699122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699180 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_699180 : Nat := 118140960795 + 699180 * 2 ^ 59
def prefixEnd_699180 : Nat := 4983230072969 + 3 ^ 40 * 699180 * 2
def baseEnd_699180 : Nat := 79781200891262153052119

theorem tailTrace_699180 : CollatzResearch.WordTrace tailWord_699180 prefixEnd_699180 79781200891262153052119 := by
  unfold tailWord_699180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750594803498872641179497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17000793071331830188239329 12750594803498872641179497)
  ·
    refine ⟨9562946102624154480884623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12750594803498872641179497 9562946102624154480884623)
    ·
      refine ⟨14344419153936231721326935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9562946102624154480884623 14344419153936231721326935)
      ·
        refine ⟨21516628730904347581990403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14344419153936231721326935 21516628730904347581990403)
        ·
          refine ⟨32274943096356521372985605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21516628730904347581990403 32274943096356521372985605)
          ·
            refine ⟨6051551830566847757434801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32274943096356521372985605 6051551830566847757434801)
            ·
              refine ⟨4538663872925135818076101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6051551830566847757434801 4538663872925135818076101)
              ·
                refine ⟨850999476173462965889269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4538663872925135818076101 850999476173462965889269)
                ·
                  refine ⟨79781200891262153052119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 850999476173462965889269 79781200891262153052119)
                  ·
                    rfl

theorem cell22_699180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_699180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699180 prefixEnd_699180 := by exact prefixLift 699180
  have htrace : WordTrace (prefixWord ++ tailWord_699180) baseStart_699180 baseEnd_699180 := by
    simpa [prefixWord, tailWord_699180, baseEnd_699180] using wordTrace_append hprefix tailTrace_699180
  have hstable : (prefixWord ++ tailWord_699180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699180).length < 2 ^ (prefixWord ++ tailWord_699180).sum := by decide
  have hdescent : baseEnd_699180 < baseStart_699180 := by decide
  rcases family_descends (prefixWord ++ tailWord_699180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699190 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_699190 : Nat := 118140960795 + 699190 * 2 ^ 59
def prefixEnd_699190 : Nat := 4983230072969 + 3 ^ 40 * 699190 * 2
def baseEnd_699190 : Nat := 239347025878149766406327

theorem tailTrace_699190 : CollatzResearch.WordTrace tailWord_699190 prefixEnd_699190 239347025878149766406327 := by
  unfold tailWord_699190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593847146060094811888939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17001036224641011326815349 1593847146060094811888939)
  ·
    refine ⟨2390770719090142217833409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593847146060094811888939 2390770719090142217833409)
    ·
      refine ⟨1793078039317606663375057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2390770719090142217833409 1793078039317606663375057)
      ·
        refine ⟨1344808529488204997531293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793078039317606663375057 1344808529488204997531293)
        ·
          refine ⟨504303198558076874074235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1344808529488204997531293 504303198558076874074235)
          ·
            refine ⟨756454797837115311111353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504303198558076874074235 756454797837115311111353)
            ·
              refine ⟨567341098377836483333515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756454797837115311111353 567341098377836483333515)
              ·
                refine ⟨851011647566754725000273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567341098377836483333515 851011647566754725000273)
                ·
                  refine ⟨638258735675066043750205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851011647566754725000273 638258735675066043750205)
                  ·
                    refine ⟨239347025878149766406327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638258735675066043750205 239347025878149766406327)
                    ·
                      rfl

theorem cell22_699190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_699190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699190 prefixEnd_699190 := by exact prefixLift 699190
  have htrace : WordTrace (prefixWord ++ tailWord_699190) baseStart_699190 baseEnd_699190 := by
    simpa [prefixWord, tailWord_699190, baseEnd_699190] using wordTrace_append hprefix tailTrace_699190
  have hstable : (prefixWord ++ tailWord_699190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699190).length < 2 ^ (prefixWord ++ tailWord_699190).sum := by decide
  have hdescent : baseEnd_699190 < baseStart_699190 := by decide
  rcases family_descends (prefixWord ++ tailWord_699190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699255 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_699255 : Nat := 118140960795 + 699255 * 2 ^ 59
def prefixEnd_699255 : Nat := 4983230072969 + 3 ^ 40 * 699255 * 2
def baseEnd_699255 : Nat := 239369276706511263531127

theorem tailTrace_699255 : CollatzResearch.WordTrace tailWord_699255 prefixEnd_699255 239369276706511263531127 := by
  unfold tailWord_699255
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503925081726033091339219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002616721150688727559479 25503925081726033091339219)
  ·
    refine ⟨38255887622589049637008829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25503925081726033091339219 38255887622589049637008829)
    ·
      refine ⟨14345957858470893613878311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38255887622589049637008829 14345957858470893613878311)
      ·
        refine ⟨21518936787706340420817467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345957858470893613878311 21518936787706340420817467)
        ·
          refine ⟨32278405181559510631226201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21518936787706340420817467 32278405181559510631226201)
          ·
            refine ⟨24208803886169632973419651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32278405181559510631226201 24208803886169632973419651)
            ·
              refine ⟨36313205829254449460129477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24208803886169632973419651 36313205829254449460129477)
              ·
                refine ⟨6808726092985209273774277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36313205829254449460129477 6808726092985209273774277)
                ·
                  refine ⟨1276636142434726738832677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6808726092985209273774277 1276636142434726738832677)
                  ·
                    refine ⟨239369276706511263531127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276636142434726738832677 239369276706511263531127)
                    ·
                      rfl

theorem cell22_699255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_699255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699255 prefixEnd_699255 := by exact prefixLift 699255
  have htrace : WordTrace (prefixWord ++ tailWord_699255) baseStart_699255 baseEnd_699255 := by
    simpa [prefixWord, tailWord_699255, baseEnd_699255] using wordTrace_append hprefix tailTrace_699255
  have hstable : (prefixWord ++ tailWord_699255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699255).length < 2 ^ (prefixWord ++ tailWord_699255).sum := by decide
  have hdescent : baseEnd_699255 < baseStart_699255 := by decide
  rcases family_descends (prefixWord ++ tailWord_699255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699257 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_699257 : Nat := 118140960795 + 699257 * 2 ^ 59
def prefixEnd_699257 : Nat := 4983230072969 + 3 ^ 40 * 699257 * 2
def baseEnd_699257 : Nat := 239369961347383924981121

theorem tailTrace_699257 : CollatzResearch.WordTrace tailWord_699257 prefixEnd_699257 239369961347383924981121 := by
  unfold tailWord_699257
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503998027718787432912025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002665351812524955274683 25503998027718787432912025)
  ·
    refine ⟨19127998520789090574684019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25503998027718787432912025 19127998520789090574684019)
    ·
      refine ⟨28691997781183635862026029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19127998520789090574684019 28691997781183635862026029)
      ·
        refine ⟨10759499167943863448259761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28691997781183635862026029 10759499167943863448259761)
        ·
          refine ⟨8069624375957897586194821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10759499167943863448259761 8069624375957897586194821)
          ·
            refine ⟨1513054570492105797411529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8069624375957897586194821 1513054570492105797411529)
            ·
              refine ⟨1134790927869079348058647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513054570492105797411529 1134790927869079348058647)
              ·
                refine ⟨1702186391803619022087971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134790927869079348058647 1702186391803619022087971)
                ·
                  refine ⟨2553279587705428533131957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702186391803619022087971 2553279587705428533131957)
                  ·
                    refine ⟨239369961347383924981121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2553279587705428533131957 239369961347383924981121)
                    ·
                      rfl

theorem cell22_699257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_699257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699257 prefixEnd_699257 := by exact prefixLift 699257
  have htrace : WordTrace (prefixWord ++ tailWord_699257) baseStart_699257 baseEnd_699257 := by
    simpa [prefixWord, tailWord_699257, baseEnd_699257] using wordTrace_append hprefix tailTrace_699257
  have hstable : (prefixWord ++ tailWord_699257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699257).length < 2 ^ (prefixWord ++ tailWord_699257).sum := by decide
  have hdescent : baseEnd_699257 < baseStart_699257 := by decide
  rcases family_descends (prefixWord ++ tailWord_699257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699272 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_699272 : Nat := 118140960795 + 699272 * 2 ^ 59
def prefixEnd_699272 : Nat := 4983230072969 + 3 ^ 40 * 699272 * 2
def baseEnd_699272 : Nat := 239375096153928885856075

theorem tailTrace_699272 : CollatzResearch.WordTrace tailWord_699272 prefixEnd_699272 239375096153928885856075 := by
  unfold tailWord_699272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12752272561332222497354035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17003030081776296663138713 12752272561332222497354035)
  ·
    refine ⟨19128408841998333746031053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12752272561332222497354035 19128408841998333746031053)
    ·
      refine ⟨7173153315749375154761645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19128408841998333746031053 7173153315749375154761645)
      ·
        refine ⟨2689932493406015683035617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7173153315749375154761645 2689932493406015683035617)
        ·
          refine ⟨2017449370054511762276713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2689932493406015683035617 2017449370054511762276713)
          ·
            refine ⟨1513087027540883821707535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017449370054511762276713 1513087027540883821707535)
            ·
              refine ⟨2269630541311325732561303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513087027540883821707535 2269630541311325732561303)
              ·
                refine ⟨3404445811966988598841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269630541311325732561303 3404445811966988598841955)
                ·
                  refine ⟨5106668717950482898262933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404445811966988598841955 5106668717950482898262933)
                  ·
                    refine ⟨239375096153928885856075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5106668717950482898262933 239375096153928885856075)
                    ·
                      rfl

theorem cell22_699272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_699272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699272 prefixEnd_699272 := by exact prefixLift 699272
  have htrace : WordTrace (prefixWord ++ tailWord_699272) baseStart_699272 baseEnd_699272 := by
    simpa [prefixWord, tailWord_699272, baseEnd_699272] using wordTrace_append hprefix tailTrace_699272
  have hstable : (prefixWord ++ tailWord_699272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699272).length < 2 ^ (prefixWord ++ tailWord_699272).sum := by decide
  have hdescent : baseEnd_699272 < baseStart_699272 := by decide
  rcases family_descends (prefixWord ++ tailWord_699272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699353 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 1, 3]
def baseStart_699353 : Nat := 118140960795 + 699353 * 2 ^ 59
def prefixEnd_699353 : Nat := 4983230072969 + 3 ^ 40 * 699353 * 2
def baseEnd_699353 : Nat := 239402824109271674580827

theorem tailTrace_699353 : CollatzResearch.WordTrace tailWord_699353 prefixEnd_699353 239402824109271674580827 := by
  unfold tailWord_699353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507499435370995828406713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17004999623580663885604475 25507499435370995828406713)
  ·
    refine ⟨19130624576528246871305035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25507499435370995828406713 19130624576528246871305035)
    ·
      refine ⟨28695936864792370306957553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19130624576528246871305035 28695936864792370306957553)
      ·
        refine ⟨21521952648594277730218165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28695936864792370306957553 21521952648594277730218165)
        ·
          refine ⟨2017683060805713537207953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21521952648594277730218165 2017683060805713537207953)
          ·
            refine ⟨1513262295604285152905965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017683060805713537207953 1513262295604285152905965)
            ·
              refine ⟨567473360851606932339737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513262295604285152905965 567473360851606932339737)
              ·
                refine ⟨425605020638705199254803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567473360851606932339737 425605020638705199254803)
                ·
                  refine ⟨638407530958057798882205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425605020638705199254803 638407530958057798882205)
                  ·
                    refine ⟨239402824109271674580827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638407530958057798882205 239402824109271674580827)
                    ·
                      rfl

theorem cell22_699353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_699353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699353 prefixEnd_699353 := by exact prefixLift 699353
  have htrace : WordTrace (prefixWord ++ tailWord_699353) baseStart_699353 baseEnd_699353 := by
    simpa [prefixWord, tailWord_699353, baseEnd_699353] using wordTrace_append hprefix tailTrace_699353
  have hstable : (prefixWord ++ tailWord_699353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699353).length < 2 ^ (prefixWord ++ tailWord_699353).sum := by decide
  have hdescent : baseEnd_699353 < baseStart_699353 := by decide
  rcases family_descends (prefixWord ++ tailWord_699353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699426 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_699426 : Nat := 118140960795 + 699426 * 2 ^ 59
def prefixEnd_699426 : Nat := 4983230072969 + 3 ^ 40 * 699426 * 2
def baseEnd_699426 : Nat := 239427813501123817505603

theorem tailTrace_699426 : CollatzResearch.WordTrace tailWord_699426 prefixEnd_699426 239427813501123817505603 := by
  unfold tailWord_699426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377540491026632323953533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17006774642737686197209421 6377540491026632323953533)
  ·
    refine ⟨2391577684134987121482575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6377540491026632323953533 2391577684134987121482575)
    ·
      refine ⟨3587366526202480682223863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391577684134987121482575 3587366526202480682223863)
      ·
        refine ⟨5381049789303721023335795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587366526202480682223863 5381049789303721023335795)
        ·
          refine ⟨8071574683955581535003693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5381049789303721023335795 8071574683955581535003693)
          ·
            refine ⟨3026840506483343075626385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8071574683955581535003693 3026840506483343075626385)
            ·
              refine ⟨2270130379862507306719789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026840506483343075626385 2270130379862507306719789)
              ·
                refine ⟨851298892448440240019921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2270130379862507306719789 851298892448440240019921)
                ·
                  refine ⟨638474169336330180014941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851298892448440240019921 638474169336330180014941)
                  ·
                    refine ⟨239427813501123817505603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638474169336330180014941 239427813501123817505603)
                    ·
                      rfl

theorem cell22_699426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_699426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699426 prefixEnd_699426 := by exact prefixLift 699426
  have htrace : WordTrace (prefixWord ++ tailWord_699426) baseStart_699426 baseEnd_699426 := by
    simpa [prefixWord, tailWord_699426, baseEnd_699426] using wordTrace_append hprefix tailTrace_699426
  have hstable : (prefixWord ++ tailWord_699426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699426).length < 2 ^ (prefixWord ++ tailWord_699426).sum := by decide
  have hdescent : baseEnd_699426 < baseStart_699426 := by decide
  rcases family_descends (prefixWord ++ tailWord_699426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699482 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_699482 : Nat := 118140960795 + 699482 * 2 ^ 59
def prefixEnd_699482 : Nat := 4983230072969 + 3 ^ 40 * 699482 * 2
def baseEnd_699482 : Nat := 239446983445558338105431

theorem tailTrace_699482 : CollatzResearch.WordTrace tailWord_699482 prefixEnd_699482 239446983445558338105431 := by
  unfold tailWord_699482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6378051112975912714963175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17008136301269100573235133 6378051112975912714963175)
  ·
    refine ⟨9567076669463869072444763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6378051112975912714963175 9567076669463869072444763)
    ·
      refine ⟨14350615004195803608667145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9567076669463869072444763 14350615004195803608667145)
      ·
        refine ⟨10762961253146852706500359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14350615004195803608667145 10762961253146852706500359)
        ·
          refine ⟨16144441879720279059750539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762961253146852706500359 16144441879720279059750539)
          ·
            refine ⟨24216662819580418589625809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16144441879720279059750539 24216662819580418589625809)
            ·
              refine ⟨18162497114685313942219357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24216662819580418589625809 18162497114685313942219357)
              ·
                refine ⟨6810936418006992728332259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18162497114685313942219357 6810936418006992728332259)
                ·
                  refine ⟨10216404627010489092498389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6810936418006992728332259 10216404627010489092498389)
                  ·
                    refine ⟨239446983445558338105431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10216404627010489092498389 239446983445558338105431)
                    ·
                      rfl

theorem cell22_699482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_699482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699482 prefixEnd_699482 := by exact prefixLift 699482
  have htrace : WordTrace (prefixWord ++ tailWord_699482) baseStart_699482 baseEnd_699482 := by
    simpa [prefixWord, tailWord_699482, baseEnd_699482] using wordTrace_append hprefix tailTrace_699482
  have hstable : (prefixWord ++ tailWord_699482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699482).length < 2 ^ (prefixWord ++ tailWord_699482).sum := by decide
  have hdescent : baseEnd_699482 < baseStart_699482 := by decide
  rcases family_descends (prefixWord ++ tailWord_699482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699512 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 8]
def baseStart_699512 : Nat := 118140960795 + 699512 * 2 ^ 59
def prefixEnd_699512 : Nat := 4983230072969 + 3 ^ 40 * 699512 * 2
def baseEnd_699512 : Nat := 79819084352882753285113

theorem tailTrace_699512 : CollatzResearch.WordTrace tailWord_699512 prefixEnd_699512 79819084352882753285113 := by
  unfold tailWord_699512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12756649320897482991722395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17008865761196643988963193 12756649320897482991722395)
  ·
    refine ⟨19134973981346224487583593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12756649320897482991722395 19134973981346224487583593)
    ·
      refine ⟨14351230486009668365687695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19134973981346224487583593 14351230486009668365687695)
      ·
        refine ⟨21526845729014502548531543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14351230486009668365687695 21526845729014502548531543)
        ·
          refine ⟨32290268593521753822797315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21526845729014502548531543 32290268593521753822797315)
          ·
            refine ⟨48435402890282630734195973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32290268593521753822797315 48435402890282630734195973)
            ·
              refine ⟨9081638041927993262661745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48435402890282630734195973 9081638041927993262661745)
              ·
                refine ⟨6811228531445994946996309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9081638041927993262661745 6811228531445994946996309)
                ·
                  refine ⟨79819084352882753285113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6811228531445994946996309 79819084352882753285113)
                  ·
                    rfl

theorem cell22_699512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_699512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699512 prefixEnd_699512 := by exact prefixLift 699512
  have htrace : WordTrace (prefixWord ++ tailWord_699512) baseStart_699512 baseEnd_699512 := by
    simpa [prefixWord, tailWord_699512, baseEnd_699512] using wordTrace_append hprefix tailTrace_699512
  have hstable : (prefixWord ++ tailWord_699512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699512).length < 2 ^ (prefixWord ++ tailWord_699512).sum := by decide
  have hdescent : baseEnd_699512 < baseStart_699512 := by decide
  rcases family_descends (prefixWord ++ tailWord_699512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699529 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 6]
def baseStart_699529 : Nat := 118140960795 + 699529 * 2 ^ 59
def prefixEnd_699529 : Nat := 4983230072969 + 3 ^ 40 * 699529 * 2
def baseEnd_699529 : Nat := 79821024168688627393429

theorem tailTrace_699529 : CollatzResearch.WordTrace tailWord_699529 prefixEnd_699529 79821024168688627393429 := by
  unfold tailWord_699529
  simp only [CollatzResearch.WordTrace]
  refine ⟨25513918682733377886813641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17009279121822251924542427 25513918682733377886813641)
  ·
    refine ⟨19135439012050033415110231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25513918682733377886813641 19135439012050033415110231)
    ·
      refine ⟨28703158518075050122665347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19135439012050033415110231 28703158518075050122665347)
      ·
        refine ⟨43054737777112575183998021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28703158518075050122665347 43054737777112575183998021)
        ·
          refine ⟨8072763333208607846999629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43054737777112575183998021 8072763333208607846999629)
          ·
            refine ⟨3027286249953227942624861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8072763333208607846999629 3027286249953227942624861)
            ·
              refine ⟨1135232343732460478484323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3027286249953227942624861 1135232343732460478484323)
              ·
                refine ⟨1702848515598690717726485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135232343732460478484323 1702848515598690717726485)
                ·
                  refine ⟨79821024168688627393429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1702848515598690717726485 79821024168688627393429)
                  ·
                    rfl

theorem cell22_699529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_699529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699529 prefixEnd_699529 := by exact prefixLift 699529
  have htrace : WordTrace (prefixWord ++ tailWord_699529) baseStart_699529 baseEnd_699529 := by
    simpa [prefixWord, tailWord_699529, baseEnd_699529] using wordTrace_append hprefix tailTrace_699529
  have hstable : (prefixWord ++ tailWord_699529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699529).length < 2 ^ (prefixWord ++ tailWord_699529).sum := by decide
  have hdescent : baseEnd_699529 < baseStart_699529 := by decide
  rcases family_descends (prefixWord ++ tailWord_699529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699548 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_699548 : Nat := 118140960795 + 699548 * 2 ^ 59
def prefixEnd_699548 : Nat := 4983230072969 + 3 ^ 40 * 699548 * 2
def baseEnd_699548 : Nat := 239469576594356165955229

theorem tailTrace_699548 : CollatzResearch.WordTrace tailWord_699548 prefixEnd_699548 239469576594356165955229 := by
  unfold tailWord_699548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757305834832272065877649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17009741113109696087836865 12757305834832272065877649)
  ·
    refine ⟨9567979376124204049408237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12757305834832272065877649 9567979376124204049408237)
    ·
      refine ⟨3587992266046576518528089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9567979376124204049408237 3587992266046576518528089)
      ·
        refine ⟨2690994199534932388896067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3587992266046576518528089 2690994199534932388896067)
        ·
          refine ⟨4036491299302398583344101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690994199534932388896067 4036491299302398583344101)
          ·
            refine ⟨756842118619199734377019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4036491299302398583344101 756842118619199734377019)
            ·
              refine ⟨1135263177928799601565529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756842118619199734377019 1135263177928799601565529)
              ·
                refine ⟨851447383446599701174147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135263177928799601565529 851447383446599701174147)
                ·
                  refine ⟨1277171075169899551761221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851447383446599701174147 1277171075169899551761221)
                  ·
                    refine ⟨239469576594356165955229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277171075169899551761221 239469576594356165955229)
                    ·
                      rfl

theorem cell22_699548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_699548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699548 prefixEnd_699548 := by exact prefixLift 699548
  have htrace : WordTrace (prefixWord ++ tailWord_699548) baseStart_699548 baseEnd_699548 := by
    simpa [prefixWord, tailWord_699548, baseEnd_699548] using wordTrace_append hprefix tailTrace_699548
  have hstable : (prefixWord ++ tailWord_699548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699548).length < 2 ^ (prefixWord ++ tailWord_699548).sum := by decide
  have hdescent : baseEnd_699548 < baseStart_699548 := by decide
  rcases family_descends (prefixWord ++ tailWord_699548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699565 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_699565 : Nat := 118140960795 + 699565 * 2 ^ 59
def prefixEnd_699565 : Nat := 4983230072969 + 3 ^ 40 * 699565 * 2
def baseEnd_699565 : Nat := 239475396041773788280177

theorem tailTrace_699565 : CollatzResearch.WordTrace tailWord_699565 prefixEnd_699565 239475396041773788280177 := by
  unfold tailWord_699565
  simp only [CollatzResearch.WordTrace]
  refine ⟨25515231710602956035124149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17010154473735304023416099 25515231710602956035124149)
  ·
    refine ⟨2392052972869027128292889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25515231710602956035124149 2392052972869027128292889)
    ·
      refine ⟨1794039729651770346219667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2392052972869027128292889 1794039729651770346219667)
      ·
        refine ⟨2691059594477655519329501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794039729651770346219667 2691059594477655519329501)
        ·
          refine ⟨1009147347929120819748563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2691059594477655519329501 1009147347929120819748563)
          ·
            refine ⟨1513721021893681229622845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009147347929120819748563 1513721021893681229622845)
            ·
              refine ⟨567645383210130461108567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513721021893681229622845 567645383210130461108567)
              ·
                refine ⟨851468074815195691662851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567645383210130461108567 851468074815195691662851)
                ·
                  refine ⟨1277202112222793537494277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851468074815195691662851 1277202112222793537494277)
                  ·
                    refine ⟨239475396041773788280177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277202112222793537494277 239475396041773788280177)
                    ·
                      rfl

theorem cell22_699565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_699565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699565 prefixEnd_699565 := by exact prefixLift 699565
  have htrace : WordTrace (prefixWord ++ tailWord_699565) baseStart_699565 baseEnd_699565 := by
    simpa [prefixWord, tailWord_699565, baseEnd_699565] using wordTrace_append hprefix tailTrace_699565
  have hstable : (prefixWord ++ tailWord_699565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699565).length < 2 ^ (prefixWord ++ tailWord_699565).sum := by decide
  have hdescent : baseEnd_699565 < baseStart_699565 := by decide
  rcases family_descends (prefixWord ++ tailWord_699565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699580 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_699580 : Nat := 118140960795 + 699580 * 2 ^ 59
def prefixEnd_699580 : Nat := 4983230072969 + 3 ^ 40 * 699580 * 2
def baseEnd_699580 : Nat := 79826843616106249718377

theorem tailTrace_699580 : CollatzResearch.WordTrace tailWord_699580 prefixEnd_699580 79826843616106249718377 := by
  unfold tailWord_699580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757889402774306798460097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17010519203699075731280129 12757889402774306798460097)
  ·
    refine ⟨9568417052080730098845073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12757889402774306798460097 9568417052080730098845073)
    ·
      refine ⟨7176312789060547574133805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9568417052080730098845073 7176312789060547574133805)
      ·
        refine ⟨2691117295897705340300177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7176312789060547574133805 2691117295897705340300177)
        ·
          refine ⟨2018337971923279005225133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691117295897705340300177 2018337971923279005225133)
          ·
            refine ⟨756876739471229626959425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2018337971923279005225133 756876739471229626959425)
            ·
              refine ⟨567657554603422220219569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756876739471229626959425 567657554603422220219569)
              ·
                refine ⟨425743165952566665164677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567657554603422220219569 425743165952566665164677)
                ·
                  refine ⟨79826843616106249718377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425743165952566665164677 79826843616106249718377)
                  ·
                    rfl

theorem cell22_699580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_699580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699580 prefixEnd_699580 := by exact prefixLift 699580
  have htrace : WordTrace (prefixWord ++ tailWord_699580) baseStart_699580 baseEnd_699580 := by
    simpa [prefixWord, tailWord_699580, baseEnd_699580] using wordTrace_append hprefix tailTrace_699580
  have hstable : (prefixWord ++ tailWord_699580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699580).length < 2 ^ (prefixWord ++ tailWord_699580).sum := by decide
  have hdescent : baseEnd_699580 < baseStart_699580 := by decide
  rcases family_descends (prefixWord ++ tailWord_699580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699696 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_699696 : Nat := 118140960795 + 699696 * 2 ^ 59
def prefixEnd_699696 : Nat := 4983230072969 + 3 ^ 40 * 699696 * 2
def baseEnd_699696 : Nat := 239520240018933113254775

theorem tailTrace_699696 : CollatzResearch.WordTrace tailWord_699696 prefixEnd_699696 239520240018933113254775 := by
  unfold tailWord_699696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12760004836564182704071471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17013339782085576938761961 12760004836564182704071471)
  ·
    refine ⟨19140007254846274056107207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12760004836564182704071471 19140007254846274056107207)
    ·
      refine ⟨28710010882269411084160811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19140007254846274056107207 28710010882269411084160811)
      ·
        refine ⟨43065016323404116626241217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28710010882269411084160811 43065016323404116626241217)
        ·
          refine ⟨32298762242553087469680913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43065016323404116626241217 32298762242553087469680913)
          ·
            refine ⟨24224071681914815602260685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32298762242553087469680913 24224071681914815602260685)
            ·
              refine ⟨9084026880718055850847757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24224071681914815602260685 9084026880718055850847757)
              ·
                refine ⟨3406510080269270944067909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9084026880718055850847757 3406510080269270944067909)
                ·
                  refine ⟨638720640050488302012733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3406510080269270944067909 638720640050488302012733)
                  ·
                    refine ⟨239520240018933113254775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638720640050488302012733 239520240018933113254775)
                    ·
                      rfl

theorem cell22_699696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_699696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699696 prefixEnd_699696 := by exact prefixLift 699696
  have htrace : WordTrace (prefixWord ++ tailWord_699696) baseStart_699696 baseEnd_699696 := by
    simpa [prefixWord, tailWord_699696, baseEnd_699696] using wordTrace_append hprefix tailTrace_699696
  have hstable : (prefixWord ++ tailWord_699696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699696).length < 2 ^ (prefixWord ++ tailWord_699696).sum := by decide
  have hdescent : baseEnd_699696 < baseStart_699696 := by decide
  rcases family_descends (prefixWord ++ tailWord_699696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699698 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_699698 : Nat := 118140960795 + 699698 * 2 ^ 59
def prefixEnd_699698 : Nat := 4983230072969 + 3 ^ 40 * 699698 * 2
def baseEnd_699698 : Nat := 79840308219935258234923

theorem tailTrace_699698 : CollatzResearch.WordTrace tailWord_699698 prefixEnd_699698 79840308219935258234923 := by
  unfold tailWord_699698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380020654780279937428937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17013388412747413166477165 6380020654780279937428937)
  ·
    refine ⟨4785015491085209953071703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6380020654780279937428937 4785015491085209953071703)
    ·
      refine ⟨7177523236627814929607555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785015491085209953071703 7177523236627814929607555)
      ·
        refine ⟨10766284854941722394411333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7177523236627814929607555 10766284854941722394411333)
        ·
          refine ⟨2018678410301572948952125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10766284854941722394411333 2018678410301572948952125)
          ·
            refine ⟨757004403863089855857047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2018678410301572948952125 757004403863089855857047)
            ·
              refine ⟨1135506605794634783785571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757004403863089855857047 1135506605794634783785571)
              ·
                refine ⟨1703259908691952175678357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135506605794634783785571 1703259908691952175678357)
                ·
                  refine ⟨79840308219935258234923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1703259908691952175678357 79840308219935258234923)
                  ·
                    rfl

theorem cell22_699698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_699698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699698 prefixEnd_699698 := by exact prefixLift 699698
  have htrace : WordTrace (prefixWord ++ tailWord_699698) baseStart_699698 baseEnd_699698 := by
    simpa [prefixWord, tailWord_699698, baseEnd_699698] using wordTrace_append hprefix tailTrace_699698
  have hstable : (prefixWord ++ tailWord_699698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699698).length < 2 ^ (prefixWord ++ tailWord_699698).sum := by decide
  have hdescent : baseEnd_699698 < baseStart_699698 := by decide
  rcases family_descends (prefixWord ++ tailWord_699698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699756 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_699756 : Nat := 118140960795 + 699756 * 2 ^ 59
def prefixEnd_699756 : Nat := 4983230072969 + 3 ^ 40 * 699756 * 2
def baseEnd_699756 : Nat := 239540779245112956754591

theorem tailTrace_699756 : CollatzResearch.WordTrace tailWord_699756 prefixEnd_699756 239540779245112956754591 := by
  unfold tailWord_699756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761099026455497827663561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17014798701940663770218081 12761099026455497827663561)
  ·
    refine ⟨9570824269841623370747671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12761099026455497827663561 9570824269841623370747671)
    ·
      refine ⟨14356236404762435056121507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9570824269841623370747671 14356236404762435056121507)
      ·
        refine ⟨21534354607143652584182261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14356236404762435056121507 21534354607143652584182261)
        ·
          refine ⟨2018845744419717429767087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21534354607143652584182261 2018845744419717429767087)
          ·
            refine ⟨3028268616629576144650631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018845744419717429767087 3028268616629576144650631)
            ·
              refine ⟨4542402924944364216975947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028268616629576144650631 4542402924944364216975947)
              ·
                refine ⟨6813604387416546325463921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542402924944364216975947 6813604387416546325463921)
                ·
                  refine ⟨5110203290562409744097941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6813604387416546325463921 5110203290562409744097941)
                  ·
                    refine ⟨239540779245112956754591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5110203290562409744097941 239540779245112956754591)
                    ·
                      rfl

theorem cell22_699756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_699756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699756 prefixEnd_699756 := by exact prefixLift 699756
  have htrace : WordTrace (prefixWord ++ tailWord_699756) baseStart_699756 baseEnd_699756 := by
    simpa [prefixWord, tailWord_699756, baseEnd_699756] using wordTrace_append hprefix tailTrace_699756
  have hstable : (prefixWord ++ tailWord_699756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699756).length < 2 ^ (prefixWord ++ tailWord_699756).sum := by decide
  have hdescent : baseEnd_699756 < baseStart_699756 := by decide
  rcases family_descends (prefixWord ++ tailWord_699756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699771 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 5]
def baseStart_699771 : Nat := 118140960795 + 699771 * 2 ^ 59
def prefixEnd_699771 : Nat := 4983230072969 + 3 ^ 40 * 699771 * 2
def baseEnd_699771 : Nat := 79848638017219305876515

theorem tailTrace_699771 : CollatzResearch.WordTrace tailWord_699771 prefixEnd_699771 79848638017219305876515 := by
  unfold tailWord_699771
  simp only [CollatzResearch.WordTrace]
  refine ⟨25522745147856653217123167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17015163431904435478082111 25522745147856653217123167)
  ·
    refine ⟨38284117721784979825684751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25522745147856653217123167 38284117721784979825684751)
    ·
      refine ⟨57426176582677469738527127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38284117721784979825684751 57426176582677469738527127)
      ·
        refine ⟨86139264874016204607790691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57426176582677469738527127 86139264874016204607790691)
        ·
          refine ⟨129208897311024306911686037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86139264874016204607790691 129208897311024306911686037)
          ·
            refine ⟨6056667061454264386485283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129208897311024306911686037 6056667061454264386485283)
            ·
              refine ⟨9085000592181396579727925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6056667061454264386485283 9085000592181396579727925)
              ·
                refine ⟨851718805517005929349493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9085000592181396579727925 851718805517005929349493)
                ·
                  refine ⟨79848638017219305876515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 851718805517005929349493 79848638017219305876515)
                  ·
                    rfl

theorem cell22_699771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 5].length) (baseStart_699771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699771 prefixEnd_699771 := by exact prefixLift 699771
  have htrace : WordTrace (prefixWord ++ tailWord_699771) baseStart_699771 baseEnd_699771 := by
    simpa [prefixWord, tailWord_699771, baseEnd_699771] using wordTrace_append hprefix tailTrace_699771
  have hstable : (prefixWord ++ tailWord_699771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699771).length < 2 ^ (prefixWord ++ tailWord_699771).sum := by decide
  have hdescent : baseEnd_699771 < baseStart_699771 := by decide
  rcases family_descends (prefixWord ++ tailWord_699771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699805 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 5]
def baseStart_699805 : Nat := 118140960795 + 699805 * 2 ^ 59
def prefixEnd_699805 : Nat := 4983230072969 + 3 ^ 40 * 699805 * 2
def baseEnd_699805 : Nat := 79852517648831054093147

theorem tailTrace_699805 : CollatzResearch.WordTrace tailWord_699805 prefixEnd_699805 79852517648831054093147 := by
  unfold tailWord_699805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25523985229733477023860869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17015990153155651349240579 25523985229733477023860869)
  ·
    refine ⟨4785747230575026941973913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25523985229733477023860869 4785747230575026941973913)
    ·
      refine ⟨3589310422931270206480435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4785747230575026941973913 3589310422931270206480435)
      ·
        refine ⟨5383965634396905309720653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589310422931270206480435 5383965634396905309720653)
        ·
          refine ⟨2018987112898839491145245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5383965634396905309720653 2018987112898839491145245)
          ·
            refine ⟨757120167337064809179467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2018987112898839491145245 757120167337064809179467)
            ·
              refine ⟨1135680251005597213769201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757120167337064809179467 1135680251005597213769201)
              ·
                refine ⟨851760188254197910326901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135680251005597213769201 851760188254197910326901)
                ·
                  refine ⟨79852517648831054093147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 851760188254197910326901 79852517648831054093147)
                  ·
                    rfl

theorem cell22_699805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_699805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699805 prefixEnd_699805 := by exact prefixLift 699805
  have htrace : WordTrace (prefixWord ++ tailWord_699805) baseStart_699805 baseEnd_699805 := by
    simpa [prefixWord, tailWord_699805, baseEnd_699805] using wordTrace_append hprefix tailTrace_699805
  have hstable : (prefixWord ++ tailWord_699805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699805).length < 2 ^ (prefixWord ++ tailWord_699805).sum := by decide
  have hdescent : baseEnd_699805 < baseStart_699805 := by decide
  rcases family_descends (prefixWord ++ tailWord_699805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699848 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_699848 : Nat := 118140960795 + 699848 * 2 ^ 59
def prefixEnd_699848 : Nat := 4983230072969 + 3 ^ 40 * 699848 * 2
def baseEnd_699848 : Nat := 239572272725255383454309

theorem tailTrace_699848 : CollatzResearch.WordTrace tailWord_699848 prefixEnd_699848 239572272725255383454309 := by
  unfold tailWord_699848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762776784288847683838099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17017035712385130245117465 12762776784288847683838099)
  ·
    refine ⟨19144165176433271525757149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12762776784288847683838099 19144165176433271525757149)
    ·
      refine ⟨7179061941162476822158931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19144165176433271525757149 7179061941162476822158931)
      ·
        refine ⟨10768592911743715233238397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179061941162476822158931 10768592911743715233238397)
        ·
          refine ⟨4038222341903893212464399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10768592911743715233238397 4038222341903893212464399)
          ·
            refine ⟨6057333512855839818696599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038222341903893212464399 6057333512855839818696599)
            ·
              refine ⟨9086000269283759728044899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057333512855839818696599 9086000269283759728044899)
              ·
                refine ⟨13629000403925639592067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9086000269283759728044899 13629000403925639592067349)
                ·
                  refine ⟨638859393934014355878157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13629000403925639592067349 638859393934014355878157)
                  ·
                    refine ⟨239572272725255383454309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638859393934014355878157 239572272725255383454309)
                    ·
                      rfl

theorem cell22_699848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_699848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699848 prefixEnd_699848 := by exact prefixLift 699848
  have htrace : WordTrace (prefixWord ++ tailWord_699848) baseStart_699848 baseEnd_699848 := by
    simpa [prefixWord, tailWord_699848, baseEnd_699848] using wordTrace_append hprefix tailTrace_699848
  have hstable : (prefixWord ++ tailWord_699848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699848).length < 2 ^ (prefixWord ++ tailWord_699848).sum := by decide
  have hdescent : baseEnd_699848 < baseStart_699848 := by decide
  rcases family_descends (prefixWord ++ tailWord_699848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699850 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_699850 : Nat := 118140960795 + 699850 * 2 ^ 59
def prefixEnd_699850 : Nat := 4983230072969 + 3 ^ 40 * 699850 * 2
def baseEnd_699850 : Nat := 79857652455376014968101

theorem tailTrace_699850 : CollatzResearch.WordTrace tailWord_699850 prefixEnd_699850 79857652455376014968101 := by
  unfold tailWord_699850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381406628642612427312251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17017084343046966472832669 6381406628642612427312251)
  ·
    refine ⟨9572109942963918640968377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381406628642612427312251 9572109942963918640968377)
    ·
      refine ⟨7179082457222938980726283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9572109942963918640968377 7179082457222938980726283)
      ·
        refine ⟨10768623685834408471089425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179082457222938980726283 10768623685834408471089425)
        ·
          refine ⟨8076467764375806353317069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10768623685834408471089425 8076467764375806353317069)
          ·
            refine ⟨3028675411640927382493901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8076467764375806353317069 3028675411640927382493901)
            ·
              refine ⟨1135753279365347768435213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3028675411640927382493901 1135753279365347768435213)
              ·
                refine ⟨425907479762005413163205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135753279365347768435213 425907479762005413163205)
                ·
                  refine ⟨79857652455376014968101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425907479762005413163205 79857652455376014968101)
                  ·
                    rfl

theorem cell22_699850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_699850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699850 prefixEnd_699850 := by exact prefixLift 699850
  have htrace : WordTrace (prefixWord ++ tailWord_699850) baseStart_699850 baseEnd_699850 := by
    simpa [prefixWord, tailWord_699850, baseEnd_699850] using wordTrace_append hprefix tailTrace_699850
  have hstable : (prefixWord ++ tailWord_699850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699850).length < 2 ^ (prefixWord ++ tailWord_699850).sum := by decide
  have hdescent : baseEnd_699850 < baseStart_699850 := by decide
  rcases family_descends (prefixWord ++ tailWord_699850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699882 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_699882 : Nat := 118140960795 + 699882 * 2 ^ 59
def prefixEnd_699882 : Nat := 4983230072969 + 3 ^ 40 * 699882 * 2
def baseEnd_699882 : Nat := 239583911620090628104205

theorem tailTrace_699882 : CollatzResearch.WordTrace tailWord_699882 prefixEnd_699882 239583911620090628104205 := by
  unfold tailWord_699882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381698412613629793603475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17017862433636346116275933 6381698412613629793603475)
  ·
    refine ⟨9572547618920444690405213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381698412613629793603475 9572547618920444690405213)
    ·
      refine ⟨3589705357095166758901955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9572547618920444690405213 3589705357095166758901955)
      ·
        refine ⟨5384558035642750138352933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589705357095166758901955 5384558035642750138352933)
        ·
          refine ⟨1009604631683015650941175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5384558035642750138352933 1009604631683015650941175)
          ·
            refine ⟨1514406947524523476411763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009604631683015650941175 1514406947524523476411763)
            ·
              refine ⟨2271610421286785214617645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514406947524523476411763 2271610421286785214617645)
              ·
                refine ⟨851853907982544455481617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271610421286785214617645 851853907982544455481617)
                ·
                  refine ⟨638890430986908341611213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851853907982544455481617 638890430986908341611213)
                  ·
                    refine ⟨239583911620090628104205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 638890430986908341611213 239583911620090628104205)
                    ·
                      rfl

theorem cell22_699882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_699882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699882 prefixEnd_699882 := by exact prefixLift 699882
  have htrace : WordTrace (prefixWord ++ tailWord_699882) baseStart_699882 baseEnd_699882 := by
    simpa [prefixWord, tailWord_699882, baseEnd_699882] using wordTrace_append hprefix tailTrace_699882
  have hstable : (prefixWord ++ tailWord_699882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699882).length < 2 ^ (prefixWord ++ tailWord_699882).sum := by decide
  have hdescent : baseEnd_699882 < baseStart_699882 := by decide
  rcases family_descends (prefixWord ++ tailWord_699882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699891 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_699891 : Nat := 118140960795 + 699891 * 2 ^ 59
def prefixEnd_699891 : Nat := 4983230072969 + 3 ^ 40 * 699891 * 2
def baseEnd_699891 : Nat := 239586992504017604629177

theorem tailTrace_699891 : CollatzResearch.WordTrace tailWord_699891 prefixEnd_699891 239586992504017604629177 := by
  unfold tailWord_699891
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527121907421913711491527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17018081271614609140994351 25527121907421913711491527)
  ·
    refine ⟨38290682861132870567237291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25527121907421913711491527 38290682861132870567237291)
    ·
      refine ⟨57436024291699305850855937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38290682861132870567237291 57436024291699305850855937)
      ·
        refine ⟨43077018218774479388141953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57436024291699305850855937 43077018218774479388141953)
        ·
          refine ⟨32307763664080859541106465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43077018218774479388141953 32307763664080859541106465)
          ·
            refine ⟨24230822748060644655829849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32307763664080859541106465 24230822748060644655829849)
            ·
              refine ⟨18173117061045483491872387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24230822748060644655829849 18173117061045483491872387)
              ·
                refine ⟨27259675591568225237808581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18173117061045483491872387 27259675591568225237808581)
                ·
                  refine ⟨5111189173419042232089109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27259675591568225237808581 5111189173419042232089109)
                  ·
                    refine ⟨239586992504017604629177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5111189173419042232089109 239586992504017604629177)
                    ·
                      rfl

theorem cell22_699891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_699891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699891 prefixEnd_699891 := by exact prefixLift 699891
  have htrace : WordTrace (prefixWord ++ tailWord_699891) baseStart_699891 baseEnd_699891 := by
    simpa [prefixWord, tailWord_699891, baseEnd_699891] using wordTrace_append hprefix tailTrace_699891
  have hstable : (prefixWord ++ tailWord_699891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699891).length < 2 ^ (prefixWord ++ tailWord_699891).sum := by decide
  have hdescent : baseEnd_699891 < baseStart_699891 := by decide
  rcases family_descends (prefixWord ++ tailWord_699891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699923 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 5]
def baseStart_699923 : Nat := 118140960795 + 699923 * 2 ^ 59
def prefixEnd_699923 : Nat := 4983230072969 + 3 ^ 40 * 699923 * 2
def baseEnd_699923 : Nat := 79865982252660062609693

theorem tailTrace_699923 : CollatzResearch.WordTrace tailWord_699923 prefixEnd_699923 79865982252660062609693 := by
  unfold tailWord_699923
  simp only [CollatzResearch.WordTrace]
  refine ⟨25528289043305983176656423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17018859362203988784437615 25528289043305983176656423)
  ·
    refine ⟨38292433564958974764984635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25528289043305983176656423 38292433564958974764984635)
    ·
      refine ⟨57438650347438462147476953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38292433564958974764984635 57438650347438462147476953)
      ·
        refine ⟨43078987760578846610607715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57438650347438462147476953 43078987760578846610607715)
        ·
          refine ⟨64618481640868269915911573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43078987760578846610607715 64618481640868269915911573)
          ·
            refine ⟨3028991326915700152308355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64618481640868269915911573 3028991326915700152308355)
            ·
              refine ⟨4543486990373550228462533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028991326915700152308355 4543486990373550228462533)
              ·
                refine ⟨851903810695040667836725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4543486990373550228462533 851903810695040667836725)
                ·
                  refine ⟨79865982252660062609693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 851903810695040667836725 79865982252660062609693)
                  ·
                    rfl

theorem cell22_699923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 5].length) (baseStart_699923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699923 prefixEnd_699923 := by exact prefixLift 699923
  have htrace : WordTrace (prefixWord ++ tailWord_699923) baseStart_699923 baseEnd_699923 := by
    simpa [prefixWord, tailWord_699923, baseEnd_699923] using wordTrace_append hprefix tailTrace_699923
  have hstable : (prefixWord ++ tailWord_699923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699923).length < 2 ^ (prefixWord ++ tailWord_699923).sum := by decide
  have hdescent : baseEnd_699923 < baseStart_699923 := by decide
  rcases family_descends (prefixWord ++ tailWord_699923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699938 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_699938 : Nat := 118140960795 + 699938 * 2 ^ 59
def prefixEnd_699938 : Nat := 4983230072969 + 3 ^ 40 * 699938 * 2
def baseEnd_699938 : Nat := 239603081564525148704033

theorem tailTrace_699938 : CollatzResearch.WordTrace tailWord_699938 prefixEnd_699938 239603081564525148704033 := by
  unfold tailWord_699938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382209034562910184613117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17019224092167760492301645 6382209034562910184613117)
  ·
    refine ⟨2393328387961091319229919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6382209034562910184613117 2393328387961091319229919)
    ·
      refine ⟨3589992581941636978844879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393328387961091319229919 3589992581941636978844879)
      ·
        refine ⟨5384988872912455468267319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3589992581941636978844879 5384988872912455468267319)
        ·
          refine ⟨8077483309368683202400979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384988872912455468267319 8077483309368683202400979)
          ·
            refine ⟨12116224964053024803601469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077483309368683202400979 12116224964053024803601469)
            ·
              refine ⟨4543584361519884301350551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12116224964053024803601469 4543584361519884301350551)
              ·
                refine ⟨6815376542279826452025827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4543584361519884301350551 6815376542279826452025827)
                ·
                  refine ⟨10223064813419739678038741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6815376542279826452025827 10223064813419739678038741)
                  ·
                    refine ⟨239603081564525148704033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10223064813419739678038741 239603081564525148704033)
                    ·
                      rfl

theorem cell22_699938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_699938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699938 prefixEnd_699938 := by exact prefixLift 699938
  have htrace : WordTrace (prefixWord ++ tailWord_699938) baseStart_699938 baseEnd_699938 := by
    simpa [prefixWord, tailWord_699938, baseEnd_699938] using wordTrace_append hprefix tailTrace_699938
  have hstable : (prefixWord ++ tailWord_699938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699938).length < 2 ^ (prefixWord ++ tailWord_699938).sum := by decide
  have hdescent : baseEnd_699938 < baseStart_699938 := by decide
  rcases family_descends (prefixWord ++ tailWord_699938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699985 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 4]
def baseStart_699985 : Nat := 118140960795 + 699985 * 2 ^ 59
def prefixEnd_699985 : Nat := 4983230072969 + 3 ^ 40 * 699985 * 2
def baseEnd_699985 : Nat := 79873056875010897592963

theorem tailTrace_699985 : CollatzResearch.WordTrace tailWord_699985 prefixEnd_699985 79873056875010897592963 := by
  unfold tailWord_699985
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530550369081367765413409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17020366912720911843608939 25530550369081367765413409)
  ·
    refine ⟨19147912776811025824060057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25530550369081367765413409 19147912776811025824060057)
    ·
      refine ⟨14360934582608269368045043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19147912776811025824060057 14360934582608269368045043)
      ·
        refine ⟨21541401873912404052067565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14360934582608269368045043 21541401873912404052067565)
        ·
          refine ⟨8078025702717151519525337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21541401873912404052067565 8078025702717151519525337)
          ·
            refine ⟨6058519277037863639644003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8078025702717151519525337 6058519277037863639644003)
            ·
              refine ⟨9087778915556795459466005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058519277037863639644003 9087778915556795459466005)
              ·
                refine ⟨425989636666724787162469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9087778915556795459466005 425989636666724787162469)
                ·
                  refine ⟨79873056875010897592963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425989636666724787162469 79873056875010897592963)
                  ·
                    rfl

theorem cell22_699985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_699985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_699985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_699985 prefixEnd_699985 := by exact prefixLift 699985
  have htrace : WordTrace (prefixWord ++ tailWord_699985) baseStart_699985 baseEnd_699985 := by
    simpa [prefixWord, tailWord_699985, baseEnd_699985] using wordTrace_append hprefix tailTrace_699985
  have hstable : (prefixWord ++ tailWord_699985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699985).length < 2 ^ (prefixWord ++ tailWord_699985).sum := by decide
  have hdescent : baseEnd_699985 < baseStart_699985 := by decide
  rcases family_descends (prefixWord ++ tailWord_699985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700043 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 6]
def baseStart_700043 : Nat := 118140960795 + 700043 * 2 ^ 59
def prefixEnd_700043 : Nat := 4983230072969 + 3 ^ 40 * 700043 * 2
def baseEnd_700043 : Nat := 239639025210339874828711

theorem tailTrace_700043 : CollatzResearch.WordTrace tailWord_700043 prefixEnd_700043 239639025210339874828711 := by
  unfold tailWord_700043
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532665802871243671024783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17021777201914162447349855 25532665802871243671024783)
  ·
    refine ⟨38298998704306865506537175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25532665802871243671024783 38298998704306865506537175)
    ·
      refine ⟨57448498056460298259805763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38298998704306865506537175 57448498056460298259805763)
      ·
        refine ⟨86172747084690447389708645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57448498056460298259805763 86172747084690447389708645)
        ·
          refine ⟨16157390078379458885570371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86172747084690447389708645 16157390078379458885570371)
          ·
            refine ⟨24236085117569188328355557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16157390078379458885570371 24236085117569188328355557)
            ·
              refine ⟨4544265959544222811566667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24236085117569188328355557 4544265959544222811566667)
              ·
                refine ⟨6816398939316334217350001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4544265959544222811566667 6816398939316334217350001)
                ·
                  refine ⟨5112299204487250663012501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6816398939316334217350001 5112299204487250663012501)
                  ·
                    refine ⟨239639025210339874828711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5112299204487250663012501 239639025210339874828711)
                    ·
                      rfl

theorem cell22_700043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_700043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700043 prefixEnd_700043 := by exact prefixLift 700043
  have htrace : WordTrace (prefixWord ++ tailWord_700043) baseStart_700043 baseEnd_700043 := by
    simpa [prefixWord, tailWord_700043, baseEnd_700043] using wordTrace_append hprefix tailTrace_700043
  have hstable : (prefixWord ++ tailWord_700043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700043).length < 2 ^ (prefixWord ++ tailWord_700043).sum := by decide
  have hdescent : baseEnd_700043 < baseStart_700043 := by decide
  rcases family_descends (prefixWord ++ tailWord_700043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700092 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_700092 : Nat := 118140960795 + 700092 * 2 ^ 59
def prefixEnd_700092 : Nat := 4983230072969 + 3 ^ 40 * 700092 * 2
def baseEnd_700092 : Nat := 79885266303906693451187

theorem tailTrace_700092 : CollatzResearch.WordTrace tailWord_700092 prefixEnd_700092 79885266303906693451187 := by
  unfold tailWord_700092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767226489846862519779265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17022968653129150026372353 12767226489846862519779265)
  ·
    refine ⟨9575419867385146889834449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12767226489846862519779265 9575419867385146889834449)
    ·
      refine ⟨7181564900538860167375837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9575419867385146889834449 7181564900538860167375837)
      ·
        refine ⟨2693086837702072562765939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7181564900538860167375837 2693086837702072562765939)
        ·
          refine ⟨4039630256553108844148909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693086837702072562765939 4039630256553108844148909)
          ·
            refine ⟨1514861346207415816555841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4039630256553108844148909 1514861346207415816555841)
            ·
              refine ⟨1136146009655561862416881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514861346207415816555841 1136146009655561862416881)
              ·
                refine ⟨852109507241671396812661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136146009655561862416881 852109507241671396812661)
                ·
                  refine ⟨79885266303906693451187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852109507241671396812661 79885266303906693451187)
                  ·
                    rfl

theorem cell22_700092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_700092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700092 prefixEnd_700092 := by exact prefixLift 700092
  have htrace : WordTrace (prefixWord ++ tailWord_700092) baseStart_700092 baseEnd_700092 := by
    simpa [prefixWord, tailWord_700092, baseEnd_700092] using wordTrace_append hprefix tailTrace_700092
  have hstable : (prefixWord ++ tailWord_700092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700092).length < 2 ^ (prefixWord ++ tailWord_700092).sum := by decide
  have hdescent : baseEnd_700092 < baseStart_700092 := by decide
  rcases family_descends (prefixWord ++ tailWord_700092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700098 : List Nat := [3, 5, 1, 2, 2, 1, 1, 7]
def baseStart_700098 : Nat := 118140960795 + 700098 * 2 ^ 59
def prefixEnd_700098 : Nat := 4983230072969 + 3 ^ 40 * 700098 * 2
def baseEnd_700098 : Nat := 26628650314926451633727

theorem tailTrace_700098 : CollatzResearch.WordTrace tailWord_700098 prefixEnd_700098 26628650314926451633727 := by
  unfold tailWord_700098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383667954417997016069237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17023114545114658709517965 6383667954417997016069237)
  ·
    refine ⟨598468870726687220256491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6383667954417997016069237 598468870726687220256491)
    ·
      refine ⟨897703306090030830384737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598468870726687220256491 897703306090030830384737)
      ·
        refine ⟨673277479567523122788553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897703306090030830384737 673277479567523122788553)
        ·
          refine ⟨504958109675642342091415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673277479567523122788553 504958109675642342091415)
          ·
            refine ⟨757437164513463513137123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504958109675642342091415 757437164513463513137123)
            ·
              refine ⟨1136155746770195269705685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757437164513463513137123 1136155746770195269705685)
              ·
                refine ⟨26628650314926451633727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1136155746770195269705685 26628650314926451633727)
                ·
                  rfl

theorem cell22_700098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_700098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700098 prefixEnd_700098 := by exact prefixLift 700098
  have htrace : WordTrace (prefixWord ++ tailWord_700098) baseStart_700098 baseEnd_700098 := by
    simpa [prefixWord, tailWord_700098, baseEnd_700098] using wordTrace_append hprefix tailTrace_700098
  have hstable : (prefixWord ++ tailWord_700098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700098).length < 2 ^ (prefixWord ++ tailWord_700098).sum := by decide
  have hdescent : baseEnd_700098 < baseStart_700098 := by decide
  rcases family_descends (prefixWord ++ tailWord_700098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700109 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 5]
def baseStart_700109 : Nat := 118140960795 + 700109 * 2 ^ 59
def prefixEnd_700109 : Nat := 4983230072969 + 3 ^ 40 * 700109 * 2
def baseEnd_700109 : Nat := 79887206119712567559503

theorem tailTrace_700109 : CollatzResearch.WordTrace tailWord_700109 prefixEnd_700109 79887206119712567559503 := by
  unfold tailWord_700109
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535073020632136942927381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17023382013754757961951587 25535073020632136942927381)
  ·
    refine ⟨1196956547842131419199721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25535073020632136942927381 1196956547842131419199721)
    ·
      refine ⟨897717410881598564399791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196956547842131419199721 897717410881598564399791)
      ·
        refine ⟨1346576116322397846599687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897717410881598564399791 1346576116322397846599687)
        ·
          refine ⟨2019864174483596769899531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346576116322397846599687 2019864174483596769899531)
          ·
            refine ⟨3029796261725395154849297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019864174483596769899531 3029796261725395154849297)
            ·
              refine ⟨2272347196294046366136973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029796261725395154849297 2272347196294046366136973)
              ·
                refine ⟨852130198610267387301365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272347196294046366136973 852130198610267387301365)
                ·
                  refine ⟨79887206119712567559503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852130198610267387301365 79887206119712567559503)
                  ·
                    rfl

theorem cell22_700109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_700109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700109 prefixEnd_700109 := by exact prefixLift 700109
  have htrace : WordTrace (prefixWord ++ tailWord_700109) baseStart_700109 baseEnd_700109 := by
    simpa [prefixWord, tailWord_700109, baseEnd_700109] using wordTrace_append hprefix tailTrace_700109
  have hstable : (prefixWord ++ tailWord_700109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700109).length < 2 ^ (prefixWord ++ tailWord_700109).sum := by decide
  have hdescent : baseEnd_700109 < baseStart_700109 := by decide
  rcases family_descends (prefixWord ++ tailWord_700109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700120 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_700120 : Nat := 118140960795 + 700120 * 2 ^ 59
def prefixEnd_700120 : Nat := 4983230072969 + 3 ^ 40 * 700120 * 2
def baseEnd_700120 : Nat := 79888461294645780217825

theorem tailTrace_700120 : CollatzResearch.WordTrace tailWord_700120 prefixEnd_700120 79888461294645780217825 := by
  unfold tailWord_700120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767737111796142910788907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17023649482394857214385209 12767737111796142910788907)
  ·
    refine ⟨19151605667694214366183361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12767737111796142910788907 19151605667694214366183361)
    ·
      refine ⟨14363704250770660774637521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19151605667694214366183361 14363704250770660774637521)
      ·
        refine ⟨10772778188077995580978141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14363704250770660774637521 10772778188077995580978141)
        ·
          refine ⟨4039791820529248342866803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10772778188077995580978141 4039791820529248342866803)
          ·
            refine ⟨6059687730793872514300205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039791820529248342866803 6059687730793872514300205)
            ·
              refine ⟨2272382899047702192862577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6059687730793872514300205 2272382899047702192862577)
              ·
                refine ⟨1704287174285776644646933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272382899047702192862577 1704287174285776644646933)
                ·
                  refine ⟨79888461294645780217825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1704287174285776644646933 79888461294645780217825)
                  ·
                    rfl

theorem cell22_700120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_700120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700120 prefixEnd_700120 := by exact prefixLift 700120
  have htrace : WordTrace (prefixWord ++ tailWord_700120) baseStart_700120 baseEnd_700120 := by
    simpa [prefixWord, tailWord_700120, baseEnd_700120] using wordTrace_append hprefix tailTrace_700120
  have hstable : (prefixWord ++ tailWord_700120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700120).length < 2 ^ (prefixWord ++ tailWord_700120).sum := by decide
  have hdescent : baseEnd_700120 < baseStart_700120 := by decide
  rcases family_descends (prefixWord ++ tailWord_700120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700152 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_700152 : Nat := 118140960795 + 700152 * 2 ^ 59
def prefixEnd_700152 : Nat := 4983230072969 + 3 ^ 40 * 700152 * 2
def baseEnd_700152 : Nat := 239676338137899923853377

theorem tailTrace_700152 : CollatzResearch.WordTrace tailWord_700152 prefixEnd_700152 239676338137899923853377 := by
  unfold tailWord_700152
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768320679738177643371355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17024427572984236857828473 12768320679738177643371355)
  ·
    refine ⟨19152481019607266465057033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12768320679738177643371355 19152481019607266465057033)
    ·
      refine ⟨14364360764705449848792775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19152481019607266465057033 14364360764705449848792775)
      ·
        refine ⟨21546541147058174773189163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14364360764705449848792775 21546541147058174773189163)
        ·
          refine ⟨32319811720587262159783745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21546541147058174773189163 32319811720587262159783745)
          ·
            refine ⟨24239858790440446619837809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32319811720587262159783745 24239858790440446619837809)
            ·
              refine ⟨18179894092830334964878357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24239858790440446619837809 18179894092830334964878357)
              ·
                refine ⟨852182535601421951478673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18179894092830334964878357 852182535601421951478673)
                ·
                  refine ⟨639136901701066463609005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 852182535601421951478673 639136901701066463609005)
                  ·
                    refine ⟨239676338137899923853377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639136901701066463609005 239676338137899923853377)
                    ·
                      rfl

theorem cell22_700152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_700152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700152 prefixEnd_700152 := by exact prefixLift 700152
  have htrace : WordTrace (prefixWord ++ tailWord_700152) baseStart_700152 baseEnd_700152 := by
    simpa [prefixWord, tailWord_700152, baseEnd_700152] using wordTrace_append hprefix tailTrace_700152
  have hstable : (prefixWord ++ tailWord_700152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700152).length < 2 ^ (prefixWord ++ tailWord_700152).sum := by decide
  have hdescent : baseEnd_700152 < baseStart_700152 := by decide
  rcases family_descends (prefixWord ++ tailWord_700152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700227 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 5]
def baseStart_700227 : Nat := 118140960795 + 700227 * 2 ^ 59
def prefixEnd_700227 : Nat := 4983230072969 + 3 ^ 40 * 700227 * 2
def baseEnd_700227 : Nat := 79900670723541576076049

theorem tailTrace_700227 : CollatzResearch.WordTrace tailWord_700227 prefixEnd_700227 79900670723541576076049 := by
  unfold tailWord_700227
  simp only [CollatzResearch.WordTrace]
  refine ⟨25539376834204643095722935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17026251222803095397148623 25539376834204643095722935)
  ·
    refine ⟨38309065251306964643584403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25539376834204643095722935 38309065251306964643584403)
    ·
      refine ⟨57463597876960446965376605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38309065251306964643584403 57463597876960446965376605)
      ·
        refine ⟨21548849203860167612016227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57463597876960446965376605 21548849203860167612016227)
        ·
          refine ⟨32323273805790251418024341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21548849203860167612016227 32323273805790251418024341)
          ·
            refine ⟨1515153459646418035219891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32323273805790251418024341 1515153459646418035219891)
            ·
              refine ⟨2272730189469627052829837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515153459646418035219891 2272730189469627052829837)
              ·
                refine ⟨852273821051110144811189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272730189469627052829837 852273821051110144811189)
                ·
                  refine ⟨79900670723541576076049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852273821051110144811189 79900670723541576076049)
                  ·
                    rfl

theorem cell22_700227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 5].length) (baseStart_700227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700227 prefixEnd_700227 := by exact prefixLift 700227
  have htrace : WordTrace (prefixWord ++ tailWord_700227) baseStart_700227 baseEnd_700227 := by
    simpa [prefixWord, tailWord_700227, baseEnd_700227] using wordTrace_append hprefix tailTrace_700227
  have hstable : (prefixWord ++ tailWord_700227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700227).length < 2 ^ (prefixWord ++ tailWord_700227).sum := by decide
  have hdescent : baseEnd_700227 < baseStart_700227 := by decide
  rcases family_descends (prefixWord ++ tailWord_700227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700287 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 6, 3]
def baseStart_700287 : Nat := 118140960795 + 700287 * 2 ^ 59
def prefixEnd_700287 : Nat := 4983230072969 + 3 ^ 40 * 700287 * 2
def baseEnd_700287 : Nat := 239722551396804571727963

theorem tailTrace_700287 : CollatzResearch.WordTrace tailWord_700287 prefixEnd_700287 239722551396804571727963 := by
  unfold tailWord_700287
  simp only [CollatzResearch.WordTrace]
  refine ⟨25541565213987273342907115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17027710142658182228604743 25541565213987273342907115)
  ·
    refine ⟨38312347820980910014360673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25541565213987273342907115 38312347820980910014360673)
    ·
      refine ⟨28734260865735682510770505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38312347820980910014360673 28734260865735682510770505)
      ·
        refine ⟨21550695649301761883077879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28734260865735682510770505 21550695649301761883077879)
        ·
          refine ⟨32326043473952642824616819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21550695649301761883077879 32326043473952642824616819)
          ·
            refine ⟨48489065210928964236925229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32326043473952642824616819 48489065210928964236925229)
            ·
              refine ⟨18183399454098361588846961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48489065210928964236925229 18183399454098361588846961)
              ·
                refine ⟨13637549590573771191635221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18183399454098361588846961 13637549590573771191635221)
                ·
                  refine ⟨639260137058145524607901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13637549590573771191635221 639260137058145524607901)
                  ·
                    refine ⟨239722551396804571727963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639260137058145524607901 239722551396804571727963)
                    ·
                      rfl

theorem cell22_700287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_700287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700287 prefixEnd_700287 := by exact prefixLift 700287
  have htrace : WordTrace (prefixWord ++ tailWord_700287) baseStart_700287 baseEnd_700287 := by
    simpa [prefixWord, tailWord_700287, baseEnd_700287] using wordTrace_append hprefix tailTrace_700287
  have hstable : (prefixWord ++ tailWord_700287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700287).length < 2 ^ (prefixWord ++ tailWord_700287).sum := by decide
  have hdescent : baseEnd_700287 < baseStart_700287 := by decide
  rcases family_descends (prefixWord ++ tailWord_700287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700306 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_700306 : Nat := 118140960795 + 700306 * 2 ^ 59
def prefixEnd_700306 : Nat := 4983230072969 + 3 ^ 40 * 700306 * 2
def baseEnd_700306 : Nat := 79909685161698285167635

theorem tailTrace_700306 : CollatzResearch.WordTrace tailWord_700306 prefixEnd_700306 79909685161698285167635 := by
  unfold tailWord_700306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6385564550229609896962193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17028172133945626391899181 6385564550229609896962193)
  ·
    refine ⟨4789173412672207422721645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6385564550229609896962193 4789173412672207422721645)
    ·
      refine ⟨1795940029752077783520617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4789173412672207422721645 1795940029752077783520617)
      ·
        refine ⟨1346955022314058337640463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795940029752077783520617 1346955022314058337640463)
        ·
          refine ⟨2020432533471087506460695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346955022314058337640463 2020432533471087506460695)
          ·
            refine ⟨3030648800206631259691043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020432533471087506460695 3030648800206631259691043)
            ·
              refine ⟨4545973200309946889536565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030648800206631259691043 4545973200309946889536565)
              ·
                refine ⟨426184987529057520894053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4545973200309946889536565 426184987529057520894053)
                ·
                  refine ⟨79909685161698285167635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426184987529057520894053 79909685161698285167635)
                  ·
                    rfl

theorem cell22_700306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_700306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700306 prefixEnd_700306 := by exact prefixLift 700306
  have htrace : WordTrace (prefixWord ++ tailWord_700306) baseStart_700306 baseEnd_700306 := by
    simpa [prefixWord, tailWord_700306, baseEnd_700306] using wordTrace_append hprefix tailTrace_700306
  have hstable : (prefixWord ++ tailWord_700306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700306).length < 2 ^ (prefixWord ++ tailWord_700306).sum := by decide
  have hdescent : baseEnd_700306 < baseStart_700306 := by decide
  rcases family_descends (prefixWord ++ tailWord_700306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700308 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_700308 : Nat := 118140960795 + 700308 * 2 ^ 59
def prefixEnd_700308 : Nat := 4983230072969 + 3 ^ 40 * 700308 * 2
def baseEnd_700308 : Nat := 239729740125967516952899

theorem tailTrace_700308 : CollatzResearch.WordTrace tailWord_700308 prefixEnd_700308 239729740125967516952899 := by
  unfold tailWord_700308
  simp only [CollatzResearch.WordTrace]
  refine ⟨12771165573455596964710789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17028220764607462619614385 12771165573455596964710789)
  ·
    refine ⟨2394593545022924430883273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12771165573455596964710789 2394593545022924430883273)
    ·
      refine ⟨1795945158767193323162455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2394593545022924430883273 1795945158767193323162455)
      ·
        refine ⟨2693917738150789984743683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795945158767193323162455 2693917738150789984743683)
        ·
          refine ⟨4040876607226184977115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693917738150789984743683 4040876607226184977115525)
          ·
            refine ⟨757664363854909683209161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4040876607226184977115525 757664363854909683209161)
            ·
              refine ⟨568248272891182262406871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757664363854909683209161 568248272891182262406871)
              ·
                refine ⟨852372409336773393610307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568248272891182262406871 852372409336773393610307)
                ·
                  refine ⟨1278558614005160090415461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852372409336773393610307 1278558614005160090415461)
                  ·
                    refine ⟨239729740125967516952899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278558614005160090415461 239729740125967516952899)
                    ·
                      rfl

theorem cell22_700308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_700308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700308 prefixEnd_700308 := by exact prefixLift 700308
  have htrace : WordTrace (prefixWord ++ tailWord_700308) baseStart_700308 baseEnd_700308 := by
    simpa [prefixWord, tailWord_700308, baseEnd_700308] using wordTrace_append hprefix tailTrace_700308
  have hstable : (prefixWord ++ tailWord_700308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700308).length < 2 ^ (prefixWord ++ tailWord_700308).sum := by decide
  have hdescent : baseEnd_700308 < baseStart_700308 := by decide
  rcases family_descends (prefixWord ++ tailWord_700308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700317 : List Nat := [1, 4, 2, 1, 2, 3, 9]
def baseStart_700317 : Nat := 118140960795 + 700317 * 2 ^ 59
def prefixEnd_700317 : Nat := 4983230072969 + 3 ^ 40 * 700317 * 2
def baseEnd_700317 : Nat := 8878993370736833091773

theorem tailTrace_700317 : CollatzResearch.WordTrace tailWord_700317 prefixEnd_700317 8878993370736833091773 := by
  unfold tailWord_700317
  simp only [CollatzResearch.WordTrace]
  refine ⟨25542659403878588466499205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17028439602585725644332803 25542659403878588466499205)
  ·
    refine ⟨4789248638227235337468601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25542659403878588466499205 4789248638227235337468601)
    ·
      refine ⟨3591936478670426503101451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4789248638227235337468601 3591936478670426503101451)
      ·
        refine ⟨5387904718005639754652177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591936478670426503101451 5387904718005639754652177)
        ·
          refine ⟨4040928538504229815989133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5387904718005639754652177 4040928538504229815989133)
          ·
            refine ⟨1515348201939086180995925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4040928538504229815989133 1515348201939086180995925)
            ·
              refine ⟨8878993370736833091773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1515348201939086180995925 8878993370736833091773)
              ·
                rfl

theorem cell22_700317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 9].length) (baseStart_700317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700317 prefixEnd_700317 := by exact prefixLift 700317
  have htrace : WordTrace (prefixWord ++ tailWord_700317) baseStart_700317 baseEnd_700317 := by
    simpa [prefixWord, tailWord_700317, baseEnd_700317] using wordTrace_append hprefix tailTrace_700317
  have hstable : (prefixWord ++ tailWord_700317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700317).length < 2 ^ (prefixWord ++ tailWord_700317).sum := by decide
  have hdescent : baseEnd_700317 < baseStart_700317 := by decide
  rcases family_descends (prefixWord ++ tailWord_700317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700321 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_700321 : Nat := 118140960795 + 700321 * 2 ^ 59
def prefixEnd_700321 : Nat := 4983230072969 + 3 ^ 40 * 700321 * 2
def baseEnd_700321 : Nat := 239734190291639816377859

theorem tailTrace_700321 : CollatzResearch.WordTrace tailWord_700321 prefixEnd_700321 239734190291639816377859 := by
  unfold tailWord_700321
  simp only [CollatzResearch.WordTrace]
  refine ⟨25542805295864097149644817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17028536863909398099763211 25542805295864097149644817)
  ·
    refine ⟨19157103971898072862233613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25542805295864097149644817 19157103971898072862233613)
    ·
      refine ⟨7183913989461777323337605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19157103971898072862233613 7183913989461777323337605)
      ·
        refine ⟨1346983873024083248125801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7183913989461777323337605 1346983873024083248125801)
        ·
          refine ⟨1010237904768062436094351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346983873024083248125801 1010237904768062436094351)
          ·
            refine ⟨1515356857152093654141527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010237904768062436094351 1515356857152093654141527)
            ·
              refine ⟨2273035285728140481212291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515356857152093654141527 2273035285728140481212291)
              ·
                refine ⟨3409552928592210721818437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273035285728140481212291 3409552928592210721818437)
                ·
                  refine ⟨639291174111039510340957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3409552928592210721818437 639291174111039510340957)
                  ·
                    refine ⟨239734190291639816377859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639291174111039510340957 239734190291639816377859)
                    ·
                      rfl

theorem cell22_700321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_700321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700321 prefixEnd_700321 := by exact prefixLift 700321
  have htrace : WordTrace (prefixWord ++ tailWord_700321) baseStart_700321 baseEnd_700321 := by
    simpa [prefixWord, tailWord_700321, baseEnd_700321] using wordTrace_append hprefix tailTrace_700321
  have hstable : (prefixWord ++ tailWord_700321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700321).length < 2 ^ (prefixWord ++ tailWord_700321).sum := by decide
  have hdescent : baseEnd_700321 < baseStart_700321 := by decide
  rcases family_descends (prefixWord ++ tailWord_700321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700362 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_700362 : Nat := 118140960795 + 700362 * 2 ^ 59
def prefixEnd_700362 : Nat := 4983230072969 + 3 ^ 40 * 700362 * 2
def baseEnd_700362 : Nat := 79916075143176458700911

theorem tailTrace_700362 : CollatzResearch.WordTrace tailWord_700362 prefixEnd_700362 79916075143176458700911 := by
  unfold tailWord_700362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6386075172178890287971835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17029533792477040767924893 6386075172178890287971835)
  ·
    refine ⟨9579112758268335431957753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6386075172178890287971835 9579112758268335431957753)
    ·
      refine ⟨7184334568701251573968315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9579112758268335431957753 7184334568701251573968315)
      ·
        refine ⟨10776501853051877360952473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7184334568701251573968315 10776501853051877360952473)
        ·
          refine ⟨8082376389788908020714355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10776501853051877360952473 8082376389788908020714355)
          ·
            refine ⟨12123564584683362031071533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082376389788908020714355 12123564584683362031071533)
            ·
              refine ⟨4546336719256260761651825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12123564584683362031071533 4546336719256260761651825)
              ·
                refine ⟨3409752539442195571238869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4546336719256260761651825 3409752539442195571238869)
                ·
                  refine ⟨79916075143176458700911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3409752539442195571238869 79916075143176458700911)
                  ·
                    rfl

theorem cell22_700362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_700362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700362 prefixEnd_700362 := by exact prefixLift 700362
  have htrace : WordTrace (prefixWord ++ tailWord_700362) baseStart_700362 baseEnd_700362 := by
    simpa [prefixWord, tailWord_700362, baseEnd_700362] using wordTrace_append hprefix tailTrace_700362
  have hstable : (prefixWord ++ tailWord_700362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700362).length < 2 ^ (prefixWord ++ tailWord_700362).sum := by decide
  have hdescent : baseEnd_700362 < baseStart_700362 := by decide
  rcases family_descends (prefixWord ++ tailWord_700362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700392 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_700392 : Nat := 118140960795 + 700392 * 2 ^ 59
def prefixEnd_700392 : Nat := 4983230072969 + 3 ^ 40 * 700392 * 2
def baseEnd_700392 : Nat := 239758495042619297852641

theorem tailTrace_700392 : CollatzResearch.WordTrace tailWord_700392 prefixEnd_700392 239758495042619297852641 := by
  unfold tailWord_700392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772697439303438137739715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17030263252404584183652953 12772697439303438137739715)
  ·
    refine ⟨19159046158955157206609573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12772697439303438137739715 19159046158955157206609573)
    ·
      refine ⟨3592321154804091976239295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19159046158955157206609573 3592321154804091976239295)
      ·
        refine ⟨5388481732206137964358943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3592321154804091976239295 5388481732206137964358943)
        ·
          refine ⟨8082722598309206946538415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5388481732206137964358943 8082722598309206946538415)
          ·
            refine ⟨12124083897463810419807623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8082722598309206946538415 12124083897463810419807623)
            ·
              refine ⟨18186125846195715629711435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12124083897463810419807623 18186125846195715629711435)
              ·
                refine ⟨27279188769293573444567153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18186125846195715629711435 27279188769293573444567153)
                ·
                  refine ⟨20459391576970180083425365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27279188769293573444567153 20459391576970180083425365)
                  ·
                    refine ⟨239758495042619297852641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20459391576970180083425365 239758495042619297852641)
                    ·
                      rfl

theorem cell22_700392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_700392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700392 prefixEnd_700392 := by exact prefixLift 700392
  have htrace : WordTrace (prefixWord ++ tailWord_700392) baseStart_700392 baseEnd_700392 := by
    simpa [prefixWord, tailWord_700392, baseEnd_700392] using wordTrace_append hprefix tailTrace_700392
  have hstable : (prefixWord ++ tailWord_700392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700392).length < 2 ^ (prefixWord ++ tailWord_700392).sum := by decide
  have hdescent : baseEnd_700392 < baseStart_700392 := by decide
  rcases family_descends (prefixWord ++ tailWord_700392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700409 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_700409 : Nat := 118140960795 + 700409 * 2 ^ 59
def prefixEnd_700409 : Nat := 4983230072969 + 3 ^ 40 * 700409 * 2
def baseEnd_700409 : Nat := 239764314490036920177589

theorem tailTrace_700409 : CollatzResearch.WordTrace tailWord_700409 prefixEnd_700409 239764314490036920177589 := by
  unfold tailWord_700409
  simp only [CollatzResearch.WordTrace]
  refine ⟨25546014919545288178848281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17030676613030192119232187 25546014919545288178848281)
  ·
    refine ⟨19159511189658966134136211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25546014919545288178848281 19159511189658966134136211)
    ·
      refine ⟨28739266784488449201204317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19159511189658966134136211 28739266784488449201204317)
      ·
        refine ⟨10777225044183168450451619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28739266784488449201204317 10777225044183168450451619)
        ·
          refine ⟨16165837566274752675677429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10777225044183168450451619 16165837566274752675677429)
          ·
            refine ⟨1515547271838258063344759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16165837566274752675677429 1515547271838258063344759)
            ·
              refine ⟨2273320907757387095017139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515547271838258063344759 2273320907757387095017139)
              ·
                refine ⟨3409981361636080642525709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273320907757387095017139 3409981361636080642525709)
                ·
                  refine ⟨1278743010613530240947141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3409981361636080642525709 1278743010613530240947141)
                  ·
                    refine ⟨239764314490036920177589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278743010613530240947141 239764314490036920177589)
                    ·
                      rfl

theorem cell22_700409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_700409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700409 prefixEnd_700409 := by exact prefixLift 700409
  have htrace : WordTrace (prefixWord ++ tailWord_700409) baseStart_700409 baseEnd_700409 := by
    simpa [prefixWord, tailWord_700409, baseEnd_700409] using wordTrace_append hprefix tailTrace_700409
  have hstable : (prefixWord ++ tailWord_700409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700409).length < 2 ^ (prefixWord ++ tailWord_700409).sum := by decide
  have hdescent : baseEnd_700409 < baseStart_700409 := by decide
  rcases family_descends (prefixWord ++ tailWord_700409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700486 : List Nat := [6, 1, 1, 1, 1, 1, 11]
def baseStart_700486 : Nat := 118140960795 + 700486 * 2 ^ 59
def prefixEnd_700486 : Nat := 4983230072969 + 3 ^ 40 * 700486 * 2
def baseEnd_700486 : Nat := 8881136043097569851939

theorem tailTrace_700486 : CollatzResearch.WordTrace tailWord_700486 prefixEnd_700486 8881136043097569851939 := by
  unfold tailWord_700486
  simp only [CollatzResearch.WordTrace]
  refine ⟨798400729383322822793791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17032548893510886886267541 798400729383322822793791)
  ·
    refine ⟨1197601094074984234190687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798400729383322822793791 1197601094074984234190687)
    ·
      refine ⟨1796401641112476351286031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197601094074984234190687 1796401641112476351286031)
      ·
        refine ⟨2694602461668714526929047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796401641112476351286031 2694602461668714526929047)
        ·
          refine ⟨4041903692503071790393571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694602461668714526929047 4041903692503071790393571)
          ·
            refine ⟨6062855538754607685590357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041903692503071790393571 6062855538754607685590357)
            ·
              refine ⟨8881136043097569851939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6062855538754607685590357 8881136043097569851939)
              ·
                rfl

theorem cell22_700486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 11].length) (baseStart_700486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700486 prefixEnd_700486 := by exact prefixLift 700486
  have htrace : WordTrace (prefixWord ++ tailWord_700486) baseStart_700486 baseEnd_700486 := by
    simpa [prefixWord, tailWord_700486, baseEnd_700486] using wordTrace_append hprefix tailTrace_700486
  have hstable : (prefixWord ++ tailWord_700486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700486).length < 2 ^ (prefixWord ++ tailWord_700486).sum := by decide
  have hdescent : baseEnd_700486 < baseStart_700486 := by decide
  rcases family_descends (prefixWord ++ tailWord_700486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700501 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_700501 : Nat := 118140960795 + 700501 * 2 ^ 59
def prefixEnd_700501 : Nat := 4983230072969 + 3 ^ 40 * 700501 * 2
def baseEnd_700501 : Nat := 239795807970179346877307

theorem tailTrace_700501 : CollatzResearch.WordTrace tailWord_700501 prefixEnd_700501 239795807970179346877307 := by
  unfold tailWord_700501
  simp only [CollatzResearch.WordTrace]
  refine ⟨25549370435211987891197357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17032913623474658594131571 25549370435211987891197357)
  ·
    refine ⟨9581013913204495459199009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25549370435211987891197357 9581013913204495459199009)
    ·
      refine ⟨7185760434903371594399257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9581013913204495459199009 7185760434903371594399257)
      ·
        refine ⟨5389320326177528695799443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7185760434903371594399257 5389320326177528695799443)
        ·
          refine ⟨8083980489266293043699165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389320326177528695799443 8083980489266293043699165)
          ·
            refine ⟨3031492683474859891387187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8083980489266293043699165 3031492683474859891387187)
            ·
              refine ⟨4547239025212289837080781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031492683474859891387187 4547239025212289837080781)
              ·
                refine ⟨1705214634454608688905293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4547239025212289837080781 1705214634454608688905293)
                ·
                  refine ⟨639455487920478258339485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1705214634454608688905293 639455487920478258339485)
                  ·
                    refine ⟨239795807970179346877307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639455487920478258339485 239795807970179346877307)
                    ·
                      rfl

theorem cell22_700501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_700501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700501 prefixEnd_700501 := by exact prefixLift 700501
  have htrace : WordTrace (prefixWord ++ tailWord_700501) baseStart_700501 baseEnd_700501 := by
    simpa [prefixWord, tailWord_700501, baseEnd_700501] using wordTrace_append hprefix tailTrace_700501
  have hstable : (prefixWord ++ tailWord_700501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700501).length < 2 ^ (prefixWord ++ tailWord_700501).sum := by decide
  have hdescent : baseEnd_700501 < baseStart_700501 := by decide
  rcases family_descends (prefixWord ++ tailWord_700501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700535 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 1, 3]
def baseStart_700535 : Nat := 118140960795 + 700535 * 2 ^ 59
def prefixEnd_700535 : Nat := 4983230072969 + 3 ^ 40 * 700535 * 2
def baseEnd_700535 : Nat := 239807446865014591527203

theorem tailTrace_700535 : CollatzResearch.WordTrace tailWord_700535 prefixEnd_700535 239807446865014591527203 := by
  unfold tailWord_700535
  simp only [CollatzResearch.WordTrace]
  refine ⟨25550610517088811697935059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17033740344725874465290039 25550610517088811697935059)
  ·
    refine ⟨38325915775633217546902589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25550610517088811697935059 38325915775633217546902589)
    ·
      refine ⟨14372218415862456580088471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38325915775633217546902589 14372218415862456580088471)
      ·
        refine ⟨21558327623793684870132707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14372218415862456580088471 21558327623793684870132707)
        ·
          refine ⟨32337491435690527305199061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21558327623793684870132707 32337491435690527305199061)
          ·
            refine ⟨757909955523996733715603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32337491435690527305199061 757909955523996733715603)
            ·
              refine ⟨1136864933285995100573405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757909955523996733715603 1136864933285995100573405)
              ·
                refine ⟨426324349982248162715027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136864933285995100573405 426324349982248162715027)
                ·
                  refine ⟨639486524973372244072541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426324349982248162715027 639486524973372244072541)
                  ·
                    refine ⟨239807446865014591527203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639486524973372244072541 239807446865014591527203)
                    ·
                      rfl

theorem cell22_700535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_700535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700535 prefixEnd_700535 := by exact prefixLift 700535
  have htrace : WordTrace (prefixWord ++ tailWord_700535) baseStart_700535 baseEnd_700535 := by
    simpa [prefixWord, tailWord_700535, baseEnd_700535] using wordTrace_append hprefix tailTrace_700535
  have hstable : (prefixWord ++ tailWord_700535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700535).length < 2 ^ (prefixWord ++ tailWord_700535).sum := by decide
  have hdescent : baseEnd_700535 < baseStart_700535 := by decide
  rcases family_descends (prefixWord ++ tailWord_700535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_700544 : Nat := 118140960795 + 700544 * 2 ^ 59
def prefixEnd_700544 : Nat := 4983230072969 + 3 ^ 40 * 700544 * 2
def baseEnd_700544 : Nat := 239810527748941568052175

theorem tailTrace_700544 : CollatzResearch.WordTrace tailWord_700544 prefixEnd_700544 239810527748941568052175 := by
  unfold tailWord_700544
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775469387028103117506343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17033959182704137490008457 12775469387028103117506343)
  ·
    refine ⟨19163204080542154676259515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12775469387028103117506343 19163204080542154676259515)
    ·
      refine ⟨28744806120813232014389273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19163204080542154676259515 28744806120813232014389273)
      ·
        refine ⟨21558604590609924010791955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28744806120813232014389273 21558604590609924010791955)
        ·
          refine ⟨32337906885914886016187933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21558604590609924010791955 32337906885914886016187933)
          ·
            refine ⟨12126715082218082256070475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32337906885914886016187933 12126715082218082256070475)
            ·
              refine ⟨18190072623327123384105713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12126715082218082256070475 18190072623327123384105713)
              ·
                refine ⟨13642554467495342538079285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18190072623327123384105713 13642554467495342538079285)
                ·
                  refine ⟨1278989481327688362944933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13642554467495342538079285 1278989481327688362944933)
                  ·
                    refine ⟨239810527748941568052175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278989481327688362944933 239810527748941568052175)
                    ·
                      rfl

theorem cell22_700544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_700544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700544 prefixEnd_700544 := by exact prefixLift 700544
  have htrace : WordTrace (prefixWord ++ tailWord_700544) baseStart_700544 baseEnd_700544 := by
    simpa [prefixWord, tailWord_700544, baseEnd_700544] using wordTrace_append hprefix tailTrace_700544
  have hstable : (prefixWord ++ tailWord_700544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700544).length < 2 ^ (prefixWord ++ tailWord_700544).sum := by decide
  have hdescent : baseEnd_700544 < baseStart_700544 := by decide
  rcases family_descends (prefixWord ++ tailWord_700544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700552 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 1, 3]
def baseStart_700552 : Nat := 118140960795 + 700552 * 2 ^ 59
def prefixEnd_700552 : Nat := 4983230072969 + 3 ^ 40 * 700552 * 2
def baseEnd_700552 : Nat := 239813266312432213852151

theorem tailTrace_700552 : CollatzResearch.WordTrace tailWord_700552 prefixEnd_700552 239813266312432213852151 := by
  unfold tailWord_700552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775615279013611800651955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17034153705351482400869273 12775615279013611800651955)
  ·
    refine ⟨19163422918520417700977933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12775615279013611800651955 19163422918520417700977933)
    ·
      refine ⟨7186283594445156637866725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19163422918520417700977933 7186283594445156637866725)
      ·
        refine ⟨1347428173958466869600011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7186283594445156637866725 1347428173958466869600011)
        ·
          refine ⟨2021142260937700304400017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347428173958466869600011 2021142260937700304400017)
          ·
            refine ⟨1515856695703275228300013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2021142260937700304400017 1515856695703275228300013)
            ·
              refine ⟨568446260888728210612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1515856695703275228300013 568446260888728210612505)
              ·
                refine ⟨426334695666546157959379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568446260888728210612505 426334695666546157959379)
                ·
                  refine ⟨639502043499819236939069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426334695666546157959379 639502043499819236939069)
                  ·
                    refine ⟨239813266312432213852151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639502043499819236939069 239813266312432213852151)
                    ·
                      rfl

theorem cell22_700552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_700552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700552 prefixEnd_700552 := by exact prefixLift 700552
  have htrace : WordTrace (prefixWord ++ tailWord_700552) baseStart_700552 baseEnd_700552 := by
    simpa [prefixWord, tailWord_700552, baseEnd_700552] using wordTrace_append hprefix tailTrace_700552
  have hstable : (prefixWord ++ tailWord_700552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700552).length < 2 ^ (prefixWord ++ tailWord_700552).sum := by decide
  have hdescent : baseEnd_700552 < baseStart_700552 := by decide
  rcases family_descends (prefixWord ++ tailWord_700552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700578 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_700578 : Nat := 118140960795 + 700578 * 2 ^ 59
def prefixEnd_700578 : Nat := 4983230072969 + 3 ^ 40 * 700578 * 2
def baseEnd_700578 : Nat := 239822166643776812702071

theorem tailTrace_700578 : CollatzResearch.WordTrace tailWord_700578 prefixEnd_700578 239822166643776812702071 := by
  unfold tailWord_700578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388044713983257510437597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17034785903955353361166925 6388044713983257510437597)
  ·
    refine ⟨2395516767743721566414099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6388044713983257510437597 2395516767743721566414099)
    ·
      refine ⟨3593275151615582349621149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395516767743721566414099 3593275151615582349621149)
      ·
        refine ⟨1347478181855843381107931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3593275151615582349621149 1347478181855843381107931)
        ·
          refine ⟨2021217272783765071661897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347478181855843381107931 2021217272783765071661897)
          ·
            refine ⟨1515912954587823803746423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2021217272783765071661897 1515912954587823803746423)
            ·
              refine ⟨2273869431881735705619635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515912954587823803746423 2273869431881735705619635)
              ·
                refine ⟨3410804147822603558429453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273869431881735705619635 3410804147822603558429453)
                ·
                  refine ⟨1279051555433476334411045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3410804147822603558429453 1279051555433476334411045)
                  ·
                    refine ⟨239822166643776812702071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279051555433476334411045 239822166643776812702071)
                    ·
                      rfl

theorem cell22_700578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_700578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700578 prefixEnd_700578 := by exact prefixLift 700578
  have htrace : WordTrace (prefixWord ++ tailWord_700578) baseStart_700578 baseEnd_700578 := by
    simpa [prefixWord, tailWord_700578, baseEnd_700578] using wordTrace_append hprefix tailTrace_700578
  have hstable : (prefixWord ++ tailWord_700578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700578).length < 2 ^ (prefixWord ++ tailWord_700578).sum := by decide
  have hdescent : baseEnd_700578 < baseStart_700578 := by decide
  rcases family_descends (prefixWord ++ tailWord_700578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700604 : List Nat := [2, 2, 2, 3, 13]
def baseStart_700604 : Nat := 118140960795 + 700604 * 2 ^ 59
def prefixEnd_700604 : Nat := 4983230072969 + 3 ^ 40 * 700604 * 2
def baseEnd_700604 : Nat := 986959123354409101037

theorem tailTrace_700604 : CollatzResearch.WordTrace tailWord_700604 prefixEnd_700604 986959123354409101037 := by
  unfold tailWord_700604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12776563576919418241098433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17035418102559224321464577 12776563576919418241098433)
  ·
    refine ⟨9582422682689563680823825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12776563576919418241098433 9582422682689563680823825)
    ·
      refine ⟨7186817012017172760617869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9582422682689563680823825 7186817012017172760617869)
      ·
        refine ⟨2695056379506439785231701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7186817012017172760617869 2695056379506439785231701)
        ·
          refine ⟨986959123354409101037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2695056379506439785231701 986959123354409101037)
          ·
            rfl

theorem cell22_700604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 13].length) (baseStart_700604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700604 prefixEnd_700604 := by exact prefixLift 700604
  have htrace : WordTrace (prefixWord ++ tailWord_700604) baseStart_700604 baseEnd_700604 := by
    simpa [prefixWord, tailWord_700604, baseEnd_700604] using wordTrace_append hprefix tailTrace_700604
  have hstable : (prefixWord ++ tailWord_700604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700604).length < 2 ^ (prefixWord ++ tailWord_700604).sum := by decide
  have hdescent : baseEnd_700604 < baseStart_700604 := by decide
  rcases family_descends (prefixWord ++ tailWord_700604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700608 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_700608 : Nat := 118140960795 + 700608 * 2 ^ 59
def prefixEnd_700608 : Nat := 4983230072969 + 3 ^ 40 * 700608 * 2
def baseEnd_700608 : Nat := 239832436256866734451979

theorem tailTrace_700608 : CollatzResearch.WordTrace tailWord_700608 prefixEnd_700608 239832436256866734451979 := by
  unfold tailWord_700608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12776636522912172582671239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17035515363882896776894985 12776636522912172582671239)
  ·
    refine ⟨19164954784368258874006859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12776636522912172582671239 19164954784368258874006859)
    ·
      refine ⟨28747432176552388311010289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19164954784368258874006859 28747432176552388311010289)
      ·
        refine ⟨21560574132414291233257717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28747432176552388311010289 21560574132414291233257717)
        ·
          refine ⟨2021303824913839803117911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21560574132414291233257717 2021303824913839803117911)
          ·
            refine ⟨3031955737370759704676867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021303824913839803117911 3031955737370759704676867)
            ·
              refine ⟨4547933606056139557015301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031955737370759704676867 4547933606056139557015301)
              ·
                refine ⟨852737551135526166940369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4547933606056139557015301 852737551135526166940369)
                ·
                  refine ⟨639553163351644625205277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 852737551135526166940369 639553163351644625205277)
                  ·
                    refine ⟨239832436256866734451979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639553163351644625205277 239832436256866734451979)
                    ·
                      rfl

theorem cell22_700608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_700608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700608 prefixEnd_700608 := by exact prefixLift 700608
  have htrace : WordTrace (prefixWord ++ tailWord_700608) baseStart_700608 baseEnd_700608 := by
    simpa [prefixWord, tailWord_700608, baseEnd_700608] using wordTrace_append hprefix tailTrace_700608
  have hstable : (prefixWord ++ tailWord_700608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700608).length < 2 ^ (prefixWord ++ tailWord_700608).sum := by decide
  have hdescent : baseEnd_700608 < baseStart_700608 := by decide
  rcases family_descends (prefixWord ++ tailWord_700608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700649 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 9]
def baseStart_700649 : Nat := 118140960795 + 700649 * 2 ^ 59
def prefixEnd_700649 : Nat := 4983230072969 + 3 ^ 40 * 700649 * 2
def baseEnd_700649 : Nat := 79948823798252098058951

theorem tailTrace_700649 : CollatzResearch.WordTrace tailWord_700649 prefixEnd_700649 79948823798252098058951 := by
  unfold tailWord_700649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554768438675809167585001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17036512292450539445056667 25554768438675809167585001)
  ·
    refine ⟨19166076329006856875688751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25554768438675809167585001 19166076329006856875688751)
    ·
      refine ⟨28749114493510285313533127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19166076329006856875688751 28749114493510285313533127)
      ·
        refine ⟨43123671740265427970299691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28749114493510285313533127 43123671740265427970299691)
        ·
          refine ⟨64685507610398141955449537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43123671740265427970299691 64685507610398141955449537)
          ·
            refine ⟨48514130707798606466587153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64685507610398141955449537 48514130707798606466587153)
            ·
              refine ⟨36385598030848954849940365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48514130707798606466587153 36385598030848954849940365)
              ·
                refine ⟨13644599261568358068727637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36385598030848954849940365 13644599261568358068727637)
                ·
                  refine ⟨79948823798252098058951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13644599261568358068727637 79948823798252098058951)
                  ·
                    rfl

theorem cell22_700649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_700649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700649 prefixEnd_700649 := by exact prefixLift 700649
  have htrace : WordTrace (prefixWord ++ tailWord_700649) baseStart_700649 baseEnd_700649 := by
    simpa [prefixWord, tailWord_700649, baseEnd_700649] using wordTrace_append hprefix tailTrace_700649
  have hstable : (prefixWord ++ tailWord_700649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700649).length < 2 ^ (prefixWord ++ tailWord_700649).sum := by decide
  have hdescent : baseEnd_700649 < baseStart_700649 := by decide
  rcases family_descends (prefixWord ++ tailWord_700649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700666 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_700666 : Nat := 118140960795 + 700666 * 2 ^ 59
def prefixEnd_700666 : Nat := 4983230072969 + 3 ^ 40 * 700666 * 2
def baseEnd_700666 : Nat := 79950763614057972167267

theorem tailTrace_700666 : CollatzResearch.WordTrace tailWord_700666 prefixEnd_700666 79950763614057972167267 := by
  unfold tailWord_700666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388847119903555267738463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17036925653076147380635901 6388847119903555267738463)
  ·
    refine ⟨9583270679855332901607695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6388847119903555267738463 9583270679855332901607695)
    ·
      refine ⟨14374906019782999352411543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583270679855332901607695 14374906019782999352411543)
      ·
        refine ⟨21562359029674499028617315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14374906019782999352411543 21562359029674499028617315)
        ·
          refine ⟨32343538544511748542925973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21562359029674499028617315 32343538544511748542925973)
          ·
            refine ⟨1516103369273988212949655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32343538544511748542925973 1516103369273988212949655)
            ·
              refine ⟨2274155053910982319424483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516103369273988212949655 2274155053910982319424483)
              ·
                refine ⟨3411232580866473479136725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274155053910982319424483 3411232580866473479136725)
                ·
                  refine ⟨79950763614057972167267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3411232580866473479136725 79950763614057972167267)
                  ·
                    rfl

theorem cell22_700666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_700666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700666 prefixEnd_700666 := by exact prefixLift 700666
  have htrace : WordTrace (prefixWord ++ tailWord_700666) baseStart_700666 baseEnd_700666 := by
    simpa [prefixWord, tailWord_700666, baseEnd_700666] using wordTrace_append hprefix tailTrace_700666
  have hstable : (prefixWord ++ tailWord_700666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700666).length < 2 ^ (prefixWord ++ tailWord_700666).sum := by decide
  have hdescent : baseEnd_700666 < baseStart_700666 := by decide
  rcases family_descends (prefixWord ++ tailWord_700666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700670 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_700670 : Nat := 118140960795 + 700670 * 2 ^ 59
def prefixEnd_700670 : Nat := 4983230072969 + 3 ^ 40 * 700670 * 2
def baseEnd_700670 : Nat := 239853660123919239401789

theorem tailTrace_700670 : CollatzResearch.WordTrace tailWord_700670 prefixEnd_700670 239853660123919239401789 := by
  unfold tailWord_700670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194441796449966219262433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17037022914399819836066309 3194441796449966219262433)
  ·
    refine ⟨2395831347337474664446825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3194441796449966219262433 2395831347337474664446825)
    ·
      refine ⟨1796873510503105998335119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2395831347337474664446825 1796873510503105998335119)
      ·
        refine ⟨2695310265754658997502679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796873510503105998335119 2695310265754658997502679)
        ·
          refine ⟨4042965398631988496254019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695310265754658997502679 4042965398631988496254019)
          ·
            refine ⟨6064448097947982744381029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4042965398631988496254019 6064448097947982744381029)
            ·
              refine ⟨1137084018365246764571443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6064448097947982744381029 1137084018365246764571443)
              ·
                refine ⟨1705626027547870146857165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137084018365246764571443 1705626027547870146857165)
                ·
                  refine ⟨639609760330451305071437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1705626027547870146857165 639609760330451305071437)
                  ·
                    refine ⟨239853660123919239401789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639609760330451305071437 239853660123919239401789)
                    ·
                      rfl

theorem cell22_700670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_700670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700670 prefixEnd_700670 := by exact prefixLift 700670
  have htrace : WordTrace (prefixWord ++ tailWord_700670) baseStart_700670 baseEnd_700670 := by
    simpa [prefixWord, tailWord_700670, baseEnd_700670] using wordTrace_append hprefix tailTrace_700670
  have hstable : (prefixWord ++ tailWord_700670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700670).length < 2 ^ (prefixWord ++ tailWord_700670).sum := by decide
  have hdescent : baseEnd_700670 < baseStart_700670 := by decide
  rcases family_descends (prefixWord ++ tailWord_700670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700681 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_700681 : Nat := 118140960795 + 700681 * 2 ^ 59
def prefixEnd_700681 : Nat := 4983230072969 + 3 ^ 40 * 700681 * 2
def baseEnd_700681 : Nat := 239857425648718877376755

theorem tailTrace_700681 : CollatzResearch.WordTrace tailWord_700681 prefixEnd_700681 239857425648718877376755 := by
  unfold tailWord_700681
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555935574559878632749897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037290383039919088499931 25555935574559878632749897)
  ·
    refine ⟨19166951680919908974562423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25555935574559878632749897 19166951680919908974562423)
    ·
      refine ⟨28750427521379863461843635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19166951680919908974562423 28750427521379863461843635)
      ·
        refine ⟨43125641282069795192765453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28750427521379863461843635 43125641282069795192765453)
        ·
          refine ⟨16172115480776173197287045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43125641282069795192765453 16172115480776173197287045)
          ·
            refine ⟨3032271652645532474491321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16172115480776173197287045 3032271652645532474491321)
            ·
              refine ⟨2274203739484149355868491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032271652645532474491321 2274203739484149355868491)
              ·
                refine ⟨3411305609226224033802737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274203739484149355868491 3411305609226224033802737)
                ·
                  refine ⟨2558479206919668025352053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411305609226224033802737 2558479206919668025352053)
                  ·
                    refine ⟨239857425648718877376755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2558479206919668025352053 239857425648718877376755)
                    ·
                      rfl

theorem cell22_700681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_700681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700681 prefixEnd_700681 := by exact prefixLift 700681
  have htrace : WordTrace (prefixWord ++ tailWord_700681) baseStart_700681 baseEnd_700681 := by
    simpa [prefixWord, tailWord_700681, baseEnd_700681] using wordTrace_append hprefix tailTrace_700681
  have hstable : (prefixWord ++ tailWord_700681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700681).length < 2 ^ (prefixWord ++ tailWord_700681).sum := by decide
  have hdescent : baseEnd_700681 < baseStart_700681 := by decide
  rcases family_descends (prefixWord ++ tailWord_700681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700683 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 5]
def baseStart_700683 : Nat := 118140960795 + 700683 * 2 ^ 59
def prefixEnd_700683 : Nat := 4983230072969 + 3 ^ 40 * 700683 * 2
def baseEnd_700683 : Nat := 79952703429863846275583

theorem tailTrace_700683 : CollatzResearch.WordTrace tailWord_700683 prefixEnd_700683 79952703429863846275583 := by
  unfold tailWord_700683
  simp only [CollatzResearch.WordTrace]
  refine ⟨25556008520552632974322703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037339013701755316215135 25556008520552632974322703)
  ·
    refine ⟨38334012780828949461484055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25556008520552632974322703 38334012780828949461484055)
    ·
      refine ⟨57501019171243424192226083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38334012780828949461484055 57501019171243424192226083)
      ·
        refine ⟨86251528756865136288339125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57501019171243424192226083 86251528756865136288339125)
        ·
          refine ⟨8086080820956106527031793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86251528756865136288339125 8086080820956106527031793)
          ·
            refine ⟨6064560615717079895273845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086080820956106527031793 6064560615717079895273845)
            ·
              refine ⟨568552557723476240181923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6064560615717079895273845 568552557723476240181923)
              ·
                refine ⟨852828836585214360272885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568552557723476240181923 852828836585214360272885)
                ·
                  refine ⟨79952703429863846275583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852828836585214360272885 79952703429863846275583)
                  ·
                    rfl

theorem cell22_700683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 5].length) (baseStart_700683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700683 prefixEnd_700683 := by exact prefixLift 700683
  have htrace : WordTrace (prefixWord ++ tailWord_700683) baseStart_700683 baseEnd_700683 := by
    simpa [prefixWord, tailWord_700683, baseEnd_700683] using wordTrace_append hprefix tailTrace_700683
  have hstable : (prefixWord ++ tailWord_700683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700683).length < 2 ^ (prefixWord ++ tailWord_700683).sum := by decide
  have hdescent : baseEnd_700683 < baseStart_700683 := by decide
  rcases family_descends (prefixWord ++ tailWord_700683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700728 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_700728 : Nat := 118140960795 + 700728 * 2 ^ 59
def prefixEnd_700728 : Nat := 4983230072969 + 3 ^ 40 * 700728 * 2
def baseEnd_700728 : Nat := 79957838236408807150537

theorem tailTrace_700728 : CollatzResearch.WordTrace tailWord_700728 prefixEnd_700728 79957838236408807150537 := by
  unfold tailWord_700728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778824902694802829855419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17038433203593070439807225 12778824902694802829855419)
  ·
    refine ⟨19168237354042204244783129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12778824902694802829855419 19168237354042204244783129)
    ·
      refine ⟨14376178015531653183587347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19168237354042204244783129 14376178015531653183587347)
      ·
        refine ⟨21564267023297479775381021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14376178015531653183587347 21564267023297479775381021)
        ·
          refine ⟨8086600133736554915767883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21564267023297479775381021 8086600133736554915767883)
          ·
            refine ⟨12129900200604832373651825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086600133736554915767883 12129900200604832373651825)
            ·
              refine ⟨9097425150453624280238869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12129900200604832373651825 9097425150453624280238869)
              ·
                refine ⟨426441803927513638136197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9097425150453624280238869 426441803927513638136197)
                ·
                  refine ⟨79957838236408807150537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426441803927513638136197 79957838236408807150537)
                  ·
                    rfl

theorem cell22_700728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_700728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700728 prefixEnd_700728 := by exact prefixLift 700728
  have htrace : WordTrace (prefixWord ++ tailWord_700728) baseStart_700728 baseEnd_700728 := by
    simpa [prefixWord, tailWord_700728, baseEnd_700728] using wordTrace_append hprefix tailTrace_700728
  have hstable : (prefixWord ++ tailWord_700728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700728).length < 2 ^ (prefixWord ++ tailWord_700728).sum := by decide
  have hdescent : baseEnd_700728 < baseStart_700728 := by decide
  rcases family_descends (prefixWord ++ tailWord_700728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700764 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_700764 : Nat := 118140960795 + 700764 * 2 ^ 59
def prefixEnd_700764 : Nat := 4983230072969 + 3 ^ 40 * 700764 * 2
def baseEnd_700764 : Nat := 239885838244934327551501

theorem tailTrace_700764 : CollatzResearch.WordTrace tailWord_700764 prefixEnd_700764 239885838244934327551501 := by
  unfold tailWord_700764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779481416629591904010673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17039308555506122538680897 12779481416629591904010673)
  ·
    refine ⟨9584611062472193928008005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12779481416629591904010673 9584611062472193928008005)
    ·
      refine ⟨1797114574213536361501501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9584611062472193928008005 1797114574213536361501501)
      ·
        refine ⟨673917965330076135563063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1797114574213536361501501 673917965330076135563063)
        ·
          refine ⟨1010876947995114203344595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673917965330076135563063 1010876947995114203344595)
          ·
            refine ⟨1516315421992671305016893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010876947995114203344595 1516315421992671305016893)
            ·
              refine ⟨568618283247251739381335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516315421992671305016893 568618283247251739381335)
              ·
                refine ⟨852927424870877609072003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568618283247251739381335 852927424870877609072003)
                ·
                  refine ⟨1279391137306316413608005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852927424870877609072003 1279391137306316413608005)
                  ·
                    refine ⟨239885838244934327551501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279391137306316413608005 239885838244934327551501)
                    ·
                      rfl

theorem cell22_700764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_700764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700764 prefixEnd_700764 := by exact prefixLift 700764
  have htrace : WordTrace (prefixWord ++ tailWord_700764) baseStart_700764 baseEnd_700764 := by
    simpa [prefixWord, tailWord_700764, baseEnd_700764] using wordTrace_append hprefix tailTrace_700764
  have hstable : (prefixWord ++ tailWord_700764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700764).length < 2 ^ (prefixWord ++ tailWord_700764).sum := by decide
  have hdescent : baseEnd_700764 < baseStart_700764 := by decide
  rcases family_descends (prefixWord ++ tailWord_700764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700835 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 5]
def baseStart_700835 : Nat := 118140960795 + 700835 * 2 ^ 59
def prefixEnd_700835 : Nat := 4983230072969 + 3 ^ 40 * 700835 * 2
def baseEnd_700835 : Nat := 79970047665304603008761

theorem tailTrace_700835 : CollatzResearch.WordTrace tailWord_700835 prefixEnd_700835 79970047665304603008761 := by
  unfold tailWord_700835
  simp only [CollatzResearch.WordTrace]
  refine ⟨25561552416001962933855959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17041034944001308622570639 25561552416001962933855959)
  ·
    refine ⟨38342328624002944400783939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25561552416001962933855959 38342328624002944400783939)
    ·
      refine ⟨57513492936004416601175909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38342328624002944400783939 57513492936004416601175909)
      ·
        refine ⟨10783779925500828112720483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57513492936004416601175909 10783779925500828112720483)
        ·
          refine ⟨16175669888251242169080725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783779925500828112720483 16175669888251242169080725)
          ·
            refine ⟨758234526011776976675659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16175669888251242169080725 758234526011776976675659)
            ·
              refine ⟨1137351789017665465013489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758234526011776976675659 1137351789017665465013489)
              ·
                refine ⟨853013841763249098760117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137351789017665465013489 853013841763249098760117)
                ·
                  refine ⟨79970047665304603008761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 853013841763249098760117 79970047665304603008761)
                  ·
                    rfl

theorem cell22_700835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 5].length) (baseStart_700835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700835 prefixEnd_700835 := by exact prefixLift 700835
  have htrace : WordTrace (prefixWord ++ tailWord_700835) baseStart_700835 baseEnd_700835 := by
    simpa [prefixWord, tailWord_700835, baseEnd_700835] using wordTrace_append hprefix tailTrace_700835
  have hstable : (prefixWord ++ tailWord_700835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700835).length < 2 ^ (prefixWord ++ tailWord_700835).sum := by decide
  have hdescent : baseEnd_700835 < baseStart_700835 := by decide
  rcases family_descends (prefixWord ++ tailWord_700835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700878 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_700878 : Nat := 118140960795 + 700878 * 2 ^ 59
def prefixEnd_700878 : Nat := 4983230072969 + 3 ^ 40 * 700878 * 2
def baseEnd_700878 : Nat := 239924862774676030201151

theorem tailTrace_700878 : CollatzResearch.WordTrace tailWord_700878 prefixEnd_700878 239924862774676030201151 := by
  unfold tailWord_700878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195390094355772659708911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17042080503230787518447525 3195390094355772659708911)
  ·
    refine ⟨4793085141533658989563367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3195390094355772659708911 4793085141533658989563367)
    ·
      refine ⟨7189627712300488484345051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793085141533658989563367 7189627712300488484345051)
      ·
        refine ⟨10784441568450732726517577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189627712300488484345051 10784441568450732726517577)
        ·
          refine ⟨8088331176338049544888183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784441568450732726517577 8088331176338049544888183)
          ·
            refine ⟨12132496764507074317332275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088331176338049544888183 12132496764507074317332275)
            ·
              refine ⟨18198745146760611475998413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12132496764507074317332275 18198745146760611475998413)
              ·
                refine ⟨6824529430035229303499405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18198745146760611475998413 6824529430035229303499405)
                ·
                  refine ⟨2559198536263210988812277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6824529430035229303499405 2559198536263210988812277)
                  ·
                    refine ⟨239924862774676030201151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2559198536263210988812277 239924862774676030201151)
                    ·
                      rfl

theorem cell22_700878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_700878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700878 prefixEnd_700878 := by exact prefixLift 700878
  have htrace : WordTrace (prefixWord ++ tailWord_700878) baseStart_700878 baseEnd_700878 := by
    simpa [prefixWord, tailWord_700878, baseEnd_700878] using wordTrace_append hprefix tailTrace_700878
  have hstable : (prefixWord ++ tailWord_700878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700878).length < 2 ^ (prefixWord ++ tailWord_700878).sum := by decide
  have hdescent : baseEnd_700878 < baseStart_700878 := by decide
  rcases family_descends (prefixWord ++ tailWord_700878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700895 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 4, 3]
def baseStart_700895 : Nat := 118140960795 + 700895 * 2 ^ 59
def prefixEnd_700895 : Nat := 4983230072969 + 3 ^ 40 * 700895 * 2
def baseEnd_700895 : Nat := 239930682222093652526099

theorem tailTrace_700895 : CollatzResearch.WordTrace tailWord_700895 prefixEnd_700895 239930682222093652526099 := by
  unfold tailWord_700895
  simp only [CollatzResearch.WordTrace]
  refine ⟨25563740795784593181040139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17042493863856395454026759 25563740795784593181040139)
  ·
    refine ⟨38345611193676889771560209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25563740795784593181040139 38345611193676889771560209)
    ·
      refine ⟨28759208395257667328670157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38345611193676889771560209 28759208395257667328670157)
      ·
        refine ⟨10784703148221625248251309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28759208395257667328670157 10784703148221625248251309)
        ·
          refine ⟨4044263680583109468094241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10784703148221625248251309 4044263680583109468094241)
          ·
            refine ⟨3033197760437332101070681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4044263680583109468094241 3033197760437332101070681)
            ·
              refine ⟨2274898320327999075803011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3033197760437332101070681 2274898320327999075803011)
              ·
                refine ⟨3412347480491998613704517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274898320327999075803011 3412347480491998613704517)
                ·
                  refine ⟨639815152592249740069597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3412347480491998613704517 639815152592249740069597)
                  ·
                    refine ⟨239930682222093652526099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639815152592249740069597 239930682222093652526099)
                    ·
                      rfl

theorem cell22_700895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_700895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700895 prefixEnd_700895 := by exact prefixLift 700895
  have htrace : WordTrace (prefixWord ++ tailWord_700895) baseStart_700895 baseEnd_700895 := by
    simpa [prefixWord, tailWord_700895, baseEnd_700895] using wordTrace_append hprefix tailTrace_700895
  have hstable : (prefixWord ++ tailWord_700895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700895).length < 2 ^ (prefixWord ++ tailWord_700895).sum := by decide
  have hdescent : baseEnd_700895 < baseStart_700895 := by decide
  rcases family_descends (prefixWord ++ tailWord_700895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700897 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 4]
def baseStart_700897 : Nat := 118140960795 + 700897 * 2 ^ 59
def prefixEnd_700897 : Nat := 4983230072969 + 3 ^ 40 * 700897 * 2
def baseEnd_700897 : Nat := 79977122287655437992031

theorem tailTrace_700897 : CollatzResearch.WordTrace tailWord_700897 prefixEnd_700897 79977122287655437992031 := by
  unfold tailWord_700897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25563813741777347522612945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17042542494518231681741963 25563813741777347522612945)
  ·
    refine ⟨19172860306333010641959709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25563813741777347522612945 19172860306333010641959709)
    ·
      refine ⟨7189822614874878990734891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19172860306333010641959709 7189822614874878990734891)
      ·
        refine ⟨10784733922312318486102337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189822614874878990734891 10784733922312318486102337)
        ·
          refine ⟨8088550441734238864576753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784733922312318486102337 8088550441734238864576753)
          ·
            refine ⟨6066412831300679148432565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8088550441734238864576753 6066412831300679148432565)
            ·
              refine ⟨568726202934438670165553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6066412831300679148432565 568726202934438670165553)
              ·
                refine ⟨426544652200829002624165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568726202934438670165553 426544652200829002624165)
                ·
                  refine ⟨79977122287655437992031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426544652200829002624165 79977122287655437992031)
                  ·
                    rfl

theorem cell22_700897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_700897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700897 prefixEnd_700897 := by exact prefixLift 700897
  have htrace : WordTrace (prefixWord ++ tailWord_700897) baseStart_700897 baseEnd_700897 := by
    simpa [prefixWord, tailWord_700897, baseEnd_700897] using wordTrace_append hprefix tailTrace_700897
  have hstable : (prefixWord ++ tailWord_700897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700897).length < 2 ^ (prefixWord ++ tailWord_700897).sum := by decide
  have hdescent : baseEnd_700897 < baseStart_700897 := by decide
  rcases family_descends (prefixWord ++ tailWord_700897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700908 : List Nat := [2, 2, 1, 1, 2, 1, 6, 7]
def baseStart_700908 : Nat := 118140960795 + 700908 * 2 ^ 59
def prefixEnd_700908 : Nat := 4983230072969 + 3 ^ 40 * 700908 * 2
def baseEnd_700908 : Nat := 26659459154196216883451

theorem tailTrace_700908 : CollatzResearch.WordTrace tailWord_700908 prefixEnd_700908 26659459154196216883451 := by
  unfold tailWord_700908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782107472368748200631689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17042809963158330934175585 12782107472368748200631689)
  ·
    refine ⟨9586580604276561150473767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12782107472368748200631689 9586580604276561150473767)
    ·
      refine ⟨14379870906414841725710651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9586580604276561150473767 14379870906414841725710651)
      ·
        refine ⟨21569806359622262588565977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14379870906414841725710651 21569806359622262588565977)
        ·
          refine ⟨16177354769716696941424483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21569806359622262588565977 16177354769716696941424483)
          ·
            refine ⟨24266032154575045412136725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16177354769716696941424483 24266032154575045412136725)
            ·
              refine ⟨1137470257245705253693909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24266032154575045412136725 1137470257245705253693909)
              ·
                refine ⟨26659459154196216883451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1137470257245705253693909 26659459154196216883451)
                ·
                  rfl

theorem cell22_700908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_700908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700908 prefixEnd_700908 := by exact prefixLift 700908
  have htrace : WordTrace (prefixWord ++ tailWord_700908) baseStart_700908 baseEnd_700908 := by
    simpa [prefixWord, tailWord_700908, baseEnd_700908] using wordTrace_append hprefix tailTrace_700908
  have hstable : (prefixWord ++ tailWord_700908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700908).length < 2 ^ (prefixWord ++ tailWord_700908).sum := by decide
  have hdescent : baseEnd_700908 < baseStart_700908 := by decide
  rcases family_descends (prefixWord ++ tailWord_700908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700974 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_700974 : Nat := 118140960795 + 700974 * 2 ^ 59
def prefixEnd_700974 : Nat := 4983230072969 + 3 ^ 40 * 700974 * 2
def baseEnd_700974 : Nat := 239957725536563779800857

theorem tailTrace_700974 : CollatzResearch.WordTrace tailWord_700974 prefixEnd_700974 239957725536563779800857 := by
  unfold tailWord_700974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195827770312298709145747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17044414774998926448777317 3195827770312298709145747)
  ·
    refine ⟨4793741655468448063718621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3195827770312298709145747 4793741655468448063718621)
    ·
      refine ⟨1797653120800668023894483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4793741655468448063718621 1797653120800668023894483)
      ·
        refine ⟨2696479681201002035841725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797653120800668023894483 2696479681201002035841725)
        ·
          refine ⟨1011179880450375763440647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2696479681201002035841725 1011179880450375763440647)
          ·
            refine ⟨1516769820675563645160971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011179880450375763440647 1516769820675563645160971)
            ·
              refine ⟨2275154731013345467741457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516769820675563645160971 2275154731013345467741457)
              ·
                refine ⟨1706366048260009100806093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275154731013345467741457 1706366048260009100806093)
                ·
                  refine ⟨639887268097503412802285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1706366048260009100806093 639887268097503412802285)
                  ·
                    refine ⟨239957725536563779800857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639887268097503412802285 239957725536563779800857)
                    ·
                      rfl

theorem cell22_700974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_700974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_700974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_700974 prefixEnd_700974 := by exact prefixLift 700974
  have htrace : WordTrace (prefixWord ++ tailWord_700974) baseStart_700974 baseEnd_700974 := by
    simpa [prefixWord, tailWord_700974, baseEnd_700974] using wordTrace_append hprefix tailTrace_700974
  have hstable : (prefixWord ++ tailWord_700974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700974).length < 2 ^ (prefixWord ++ tailWord_700974).sum := by decide
  have hdescent : baseEnd_700974 < baseStart_700974 := by decide
  rcases family_descends (prefixWord ++ tailWord_700974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701015 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 6]
def baseStart_701015 : Nat := 118140960795 + 701015 * 2 ^ 59
def prefixEnd_701015 : Nat := 4983230072969 + 3 ^ 40 * 701015 * 2
def baseEnd_701015 : Nat := 79990586891484446508577

theorem tailTrace_701015 : CollatzResearch.WordTrace tailWord_701015 prefixEnd_701015 79990586891484446508577 := by
  unfold tailWord_701015
  simp only [CollatzResearch.WordTrace]
  refine ⟨25568117555349853675408499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17045411703566569116938999 25568117555349853675408499)
  ·
    refine ⟨38352176333024780513112749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25568117555349853675408499 38352176333024780513112749)
    ·
      refine ⟨14382066124884292692417281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38352176333024780513112749 14382066124884292692417281)
      ·
        refine ⟨10786549593663219519312961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14382066124884292692417281 10786549593663219519312961)
        ·
          refine ⟨8089912195247414639484721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10786549593663219519312961 8089912195247414639484721)
          ·
            refine ⟨6067434146435560979613541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8089912195247414639484721 6067434146435560979613541)
            ·
              refine ⟨1137643902456667683677539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6067434146435560979613541 1137643902456667683677539)
              ·
                refine ⟨1706465853685001525516309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137643902456667683677539 1706465853685001525516309)
                ·
                  refine ⟨79990586891484446508577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1706465853685001525516309 79990586891484446508577)
                  ·
                    rfl

theorem cell22_701015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 6].length) (baseStart_701015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701015 prefixEnd_701015 := by exact prefixLift 701015
  have htrace : WordTrace (prefixWord ++ tailWord_701015) baseStart_701015 baseEnd_701015 := by
    simpa [prefixWord, tailWord_701015, baseEnd_701015] using wordTrace_append hprefix tailTrace_701015
  have hstable : (prefixWord ++ tailWord_701015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701015).length < 2 ^ (prefixWord ++ tailWord_701015).sum := by decide
  have hdescent : baseEnd_701015 < baseStart_701015 := by decide
  rcases family_descends (prefixWord ++ tailWord_701015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701049 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 4]
def baseStart_701049 : Nat := 118140960795 + 701049 * 2 ^ 59
def prefixEnd_701049 : Nat := 4983230072969 + 3 ^ 40 * 701049 * 2
def baseEnd_701049 : Nat := 79994466523096194725209

theorem tailTrace_701049 : CollatzResearch.WordTrace tailWord_701049 prefixEnd_701049 79994466523096194725209 := by
  unfold tailWord_701049
  simp only [CollatzResearch.WordTrace]
  refine ⟨25569357637226677482146201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17046238424817784988097467 25569357637226677482146201)
  ·
    refine ⟨19177018227920008111609651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25569357637226677482146201 19177018227920008111609651)
    ·
      refine ⟨28765527341880012167414477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19177018227920008111609651 28765527341880012167414477)
      ·
        refine ⟨10787072753205004562780429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28765527341880012167414477 10787072753205004562780429)
        ·
          refine ⟨4045152282451876711042661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10787072753205004562780429 4045152282451876711042661)
          ·
            refine ⟨758466052959726883320499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4045152282451876711042661 758466052959726883320499)
            ·
              refine ⟨1137699079439590324980749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758466052959726883320499 1137699079439590324980749)
              ·
                refine ⟨426637154789846371867781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137699079439590324980749 426637154789846371867781)
                ·
                  refine ⟨79994466523096194725209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426637154789846371867781 79994466523096194725209)
                  ·
                    rfl

theorem cell22_701049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_701049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701049 prefixEnd_701049 := by exact prefixLift 701049
  have htrace : WordTrace (prefixWord ++ tailWord_701049) baseStart_701049 baseEnd_701049 := by
    simpa [prefixWord, tailWord_701049, baseEnd_701049] using wordTrace_append hprefix tailTrace_701049
  have hstable : (prefixWord ++ tailWord_701049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701049).length < 2 ^ (prefixWord ++ tailWord_701049).sum := by decide
  have hdescent : baseEnd_701049 < baseStart_701049 := by decide
  rcases family_descends (prefixWord ++ tailWord_701049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701060 : List Nat := [2, 3, 2, 1, 3, 1, 10]
def baseStart_701060 : Nat := 118140960795 + 701060 * 2 ^ 59
def prefixEnd_701060 : Nat := 4983230072969 + 3 ^ 40 * 701060 * 2
def baseEnd_701060 : Nat := 8888413522003267487059

theorem tailTrace_701060 : CollatzResearch.WordTrace tailWord_701060 prefixEnd_701060 8888413522003267487059 := by
  unfold tailWord_701060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784879420093413180398317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17046505893457884240531089 12784879420093413180398317)
  ·
    refine ⟨4794329782535029942649369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12784879420093413180398317 4794329782535029942649369)
    ·
      refine ⟨3595747336901272456987027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4794329782535029942649369 3595747336901272456987027)
      ·
        refine ⟨5393621005351908685480541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595747336901272456987027 5393621005351908685480541)
        ·
          refine ⟨2022607877006965757055203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5393621005351908685480541 2022607877006965757055203)
          ·
            refine ⟨3033911815510448635582805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022607877006965757055203 3033911815510448635582805)
            ·
              refine ⟨8888413522003267487059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3033911815510448635582805 8888413522003267487059)
              ·
                rfl

theorem cell22_701060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 10].length) (baseStart_701060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701060 prefixEnd_701060 := by exact prefixLift 701060
  have htrace : WordTrace (prefixWord ++ tailWord_701060) baseStart_701060 baseEnd_701060 := by
    simpa [prefixWord, tailWord_701060, baseEnd_701060] using wordTrace_append hprefix tailTrace_701060
  have hstable : (prefixWord ++ tailWord_701060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701060).length < 2 ^ (prefixWord ++ tailWord_701060).sum := by decide
  have hdescent : baseEnd_701060 < baseStart_701060 := by decide
  rcases family_descends (prefixWord ++ tailWord_701060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701066 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_701066 : Nat := 118140960795 + 701066 * 2 ^ 59
def prefixEnd_701066 : Nat := 4983230072969 + 3 ^ 40 * 701066 * 2
def baseEnd_701066 : Nat := 79996406338902068833525

theorem tailTrace_701066 : CollatzResearch.WordTrace tailWord_701066 prefixEnd_701066 79996406338902068833525 := by
  unfold tailWord_701066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6392494419541272346378763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17046651785443392923676701 6392494419541272346378763)
  ·
    refine ⟨9588741629311908519568145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6392494419541272346378763 9588741629311908519568145)
    ·
      refine ⟨7191556221983931389676109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9588741629311908519568145 7191556221983931389676109)
      ·
        refine ⟨2696833583243974271128541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7191556221983931389676109 2696833583243974271128541)
        ·
          refine ⟨1011312593716490351673203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2696833583243974271128541 1011312593716490351673203)
          ·
            refine ⟨1516968890574735527509805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011312593716490351673203 1516968890574735527509805)
            ·
              refine ⟨568863333965525822816177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516968890574735527509805 568863333965525822816177)
              ·
                refine ⟨426647500474144367112133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568863333965525822816177 426647500474144367112133)
                ·
                  refine ⟨79996406338902068833525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426647500474144367112133 79996406338902068833525)
                  ·
                    rfl

theorem cell22_701066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_701066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701066 prefixEnd_701066 := by exact prefixLift 701066
  have htrace : WordTrace (prefixWord ++ tailWord_701066) baseStart_701066 baseEnd_701066 := by
    simpa [prefixWord, tailWord_701066, baseEnd_701066] using wordTrace_append hprefix tailTrace_701066
  have hstable : (prefixWord ++ tailWord_701066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701066).length < 2 ^ (prefixWord ++ tailWord_701066).sum := by decide
  have hdescent : baseEnd_701066 < baseStart_701066 := by decide
  rcases family_descends (prefixWord ++ tailWord_701066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701092 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_701092 : Nat := 118140960795 + 701092 * 2 ^ 59
def prefixEnd_701092 : Nat := 4983230072969 + 3 ^ 40 * 701092 * 2
def baseEnd_701092 : Nat := 239998119348050805350495

theorem tailTrace_701092 : CollatzResearch.WordTrace tailWord_701092 prefixEnd_701092 239998119348050805350495 := by
  unfold tailWord_701092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12785462988035447912980765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17047283984047263883974353 12785462988035447912980765)
  ·
    refine ⟨4794548620513292967367787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12785462988035447912980765 4794548620513292967367787)
    ·
      refine ⟨7191822930769939451051681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4794548620513292967367787 7191822930769939451051681)
      ·
        refine ⟨5393867198077454588288761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7191822930769939451051681 5393867198077454588288761)
        ·
          refine ⟨4045400398558090941216571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5393867198077454588288761 4045400398558090941216571)
          ·
            refine ⟨6068100597837136411824857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045400398558090941216571 6068100597837136411824857)
            ·
              refine ⟨4551075448377852308868643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068100597837136411824857 4551075448377852308868643)
              ·
                refine ⟨6826613172566778463302965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551075448377852308868643 6826613172566778463302965)
                ·
                  refine ⟨639994984928135480934653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6826613172566778463302965 639994984928135480934653)
                  ·
                    refine ⟨239998119348050805350495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639994984928135480934653 239998119348050805350495)
                    ·
                      rfl

theorem cell22_701092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_701092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701092 prefixEnd_701092 := by exact prefixLift 701092
  have htrace : WordTrace (prefixWord ++ tailWord_701092) baseStart_701092 baseEnd_701092 := by
    simpa [prefixWord, tailWord_701092, baseEnd_701092] using wordTrace_append hprefix tailTrace_701092
  have hstable : (prefixWord ++ tailWord_701092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701092).length < 2 ^ (prefixWord ++ tailWord_701092).sum := by decide
  have hdescent : baseEnd_701092 < baseStart_701092 := by decide
  rcases family_descends (prefixWord ++ tailWord_701092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701152 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_701152 : Nat := 118140960795 + 701152 * 2 ^ 59
def prefixEnd_701152 : Nat := 4983230072969 + 3 ^ 40 * 701152 * 2
def baseEnd_701152 : Nat := 240018658574230648850311

theorem tailTrace_701152 : CollatzResearch.WordTrace tailWord_701152 prefixEnd_701152 240018658574230648850311 := by
  unfold tailWord_701152
  simp only [CollatzResearch.WordTrace]
  refine ⟨12786557177926763036572855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17048742903902350715430473 12786557177926763036572855)
  ·
    refine ⟨19179835766890144554859283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12786557177926763036572855 19179835766890144554859283)
    ·
      refine ⟨28769753650335216832288925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19179835766890144554859283 28769753650335216832288925)
      ·
        refine ⟨10788657618875706312108347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28769753650335216832288925 10788657618875706312108347)
        ·
          refine ⟨16182986428313559468162521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10788657618875706312108347 16182986428313559468162521)
          ·
            refine ⟨12137239821235169601121891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16182986428313559468162521 12137239821235169601121891)
            ·
              refine ⟨18205859731852754401682837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137239821235169601121891 18205859731852754401682837)
              ·
                refine ⟨853399674930597862578883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18205859731852754401682837 853399674930597862578883)
                ·
                  refine ⟨1280099512395896793868325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853399674930597862578883 1280099512395896793868325)
                  ·
                    refine ⟨240018658574230648850311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1280099512395896793868325 240018658574230648850311)
                    ·
                      rfl

theorem cell22_701152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_701152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701152 prefixEnd_701152 := by exact prefixLift 701152
  have htrace : WordTrace (prefixWord ++ tailWord_701152) baseStart_701152 baseEnd_701152 := by
    simpa [prefixWord, tailWord_701152, baseEnd_701152] using wordTrace_append hprefix tailTrace_701152
  have hstable : (prefixWord ++ tailWord_701152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701152).length < 2 ^ (prefixWord ++ tailWord_701152).sum := by decide
  have hdescent : baseEnd_701152 < baseStart_701152 := by decide
  rcases family_descends (prefixWord ++ tailWord_701152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701195 : List Nat := [1, 1, 1, 1, 5, 1, 1, 11]
def baseStart_701195 : Nat := 118140960795 + 701195 * 2 ^ 59
def prefixEnd_701195 : Nat := 4983230072969 + 3 ^ 40 * 701195 * 2
def baseEnd_701195 : Nat := 26670375372554763336131

theorem tailTrace_701195 : CollatzResearch.WordTrace tailWord_701195 prefixEnd_701195 26670375372554763336131 := by
  unfold tailWord_701195
  simp only [CollatzResearch.WordTrace]
  refine ⟨25574682694697744416961039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17049788463131829611307359 25574682694697744416961039)
  ·
    refine ⟨38362024042046616625441559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25574682694697744416961039 38362024042046616625441559)
    ·
      refine ⟨57543036063069924938162339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38362024042046616625441559 57543036063069924938162339)
      ·
        refine ⟨86314554094604887407243509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57543036063069924938162339 86314554094604887407243509)
        ·
          refine ⟨8091989446369208194429079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86314554094604887407243509 8091989446369208194429079)
          ·
            refine ⟨12137984169553812291643619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091989446369208194429079 12137984169553812291643619)
            ·
              refine ⟨18206976254330718437465429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137984169553812291643619 18206976254330718437465429)
              ·
                refine ⟨26670375372554763336131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18206976254330718437465429 26670375372554763336131)
                ·
                  rfl

theorem cell22_701195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 11].length) (baseStart_701195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701195 prefixEnd_701195 := by exact prefixLift 701195
  have htrace : WordTrace (prefixWord ++ tailWord_701195) baseStart_701195 baseEnd_701195 := by
    simpa [prefixWord, tailWord_701195, baseEnd_701195] using wordTrace_append hprefix tailTrace_701195
  have hstable : (prefixWord ++ tailWord_701195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701195).length < 2 ^ (prefixWord ++ tailWord_701195).sum := by decide
  have hdescent : baseEnd_701195 < baseStart_701195 := by decide
  rcases family_descends (prefixWord ++ tailWord_701195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701212 : List Nat := [2, 2, 3, 1, 1, 4, 1, 8]
def baseStart_701212 : Nat := 118140960795 + 701212 * 2 ^ 59
def prefixEnd_701212 : Nat := 4983230072969 + 3 ^ 40 * 701212 * 2
def baseEnd_701212 : Nat := 26671021977823388038903

theorem tailTrace_701212 : CollatzResearch.WordTrace tailWord_701212 prefixEnd_701212 26671021977823388038903 := by
  unfold tailWord_701212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787651367818078160164945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17050201823757437546886593 12787651367818078160164945)
  ·
    refine ⟨9590738525863558620123709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12787651367818078160164945 9590738525863558620123709)
    ·
      refine ⟨3596526947198834482546391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9590738525863558620123709 3596526947198834482546391)
      ·
        refine ⟨5394790420798251723819587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596526947198834482546391 5394790420798251723819587)
        ·
          refine ⟨8092185631197377585729381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394790420798251723819587 8092185631197377585729381)
          ·
            refine ⟨1517284805849508297324259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8092185631197377585729381 1517284805849508297324259)
            ·
              refine ⟨2275927208774262445986389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517284805849508297324259 2275927208774262445986389)
              ·
                refine ⟨26671021977823388038903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2275927208774262445986389 26671021977823388038903)
                ·
                  rfl

theorem cell22_701212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_701212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701212 prefixEnd_701212 := by exact prefixLift 701212
  have htrace : WordTrace (prefixWord ++ tailWord_701212) baseStart_701212 baseEnd_701212 := by
    simpa [prefixWord, tailWord_701212, baseEnd_701212] using wordTrace_append hprefix tailTrace_701212
  have hstable : (prefixWord ++ tailWord_701212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701212).length < 2 ^ (prefixWord ++ tailWord_701212).sum := by decide
  have hdescent : baseEnd_701212 < baseStart_701212 := by decide
  rcases family_descends (prefixWord ++ tailWord_701212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701227 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 7, 3]
def baseStart_701227 : Nat := 118140960795 + 701227 * 2 ^ 59
def prefixEnd_701227 : Nat := 4983230072969 + 3 ^ 40 * 701227 * 2
def baseEnd_701227 : Nat := 240044332606955453225081

theorem tailTrace_701227 : CollatzResearch.WordTrace tailWord_701227 prefixEnd_701227 240044332606955453225081 := by
  unfold tailWord_701227
  simp only [CollatzResearch.WordTrace]
  refine ⟨25575849830581813882125935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17050566553721209254750623 25575849830581813882125935)
  ·
    refine ⟨38363774745872720823188903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25575849830581813882125935 38363774745872720823188903)
    ·
      refine ⟨57545662118809081234783355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38363774745872720823188903 57545662118809081234783355)
      ·
        refine ⟨86318493178213621852175033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57545662118809081234783355 86318493178213621852175033)
        ·
          refine ⟨64738869883660216389131275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86318493178213621852175033 64738869883660216389131275)
          ·
            refine ⟨97108304825490324583696913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64738869883660216389131275 97108304825490324583696913)
            ·
              refine ⟨72831228619117743437772685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97108304825490324583696913 72831228619117743437772685)
              ·
                refine ⟨27311710732169153789164757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72831228619117743437772685 27311710732169153789164757)
                ·
                  refine ⟨640118220285214541933549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 27311710732169153789164757 640118220285214541933549)
                  ·
                    refine ⟨240044332606955453225081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640118220285214541933549 240044332606955453225081)
                    ·
                      rfl

theorem cell22_701227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3].length) (baseStart_701227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701227 prefixEnd_701227 := by exact prefixLift 701227
  have htrace : WordTrace (prefixWord ++ tailWord_701227) baseStart_701227 baseEnd_701227 := by
    simpa [prefixWord, tailWord_701227, baseEnd_701227] using wordTrace_append hprefix tailTrace_701227
  have hstable : (prefixWord ++ tailWord_701227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701227).length < 2 ^ (prefixWord ++ tailWord_701227).sum := by decide
  have hdescent : baseEnd_701227 < baseStart_701227 := by decide
  rcases family_descends (prefixWord ++ tailWord_701227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701319 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 6]
def baseStart_701319 : Nat := 118140960795 + 701319 * 2 ^ 59
def prefixEnd_701319 : Nat := 4983230072969 + 3 ^ 40 * 701319 * 2
def baseEnd_701319 : Nat := 80025275362365959974933

theorem tailTrace_701319 : CollatzResearch.WordTrace tailWord_701319 prefixEnd_701319 80025275362365959974933 := by
  unfold tailWord_701319
  simp only [CollatzResearch.WordTrace]
  refine ⟨25579205346248513594475011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17052803564165675729650007 25579205346248513594475011)
  ·
    refine ⟨38368808019372770391712517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25579205346248513594475011 38368808019372770391712517)
    ·
      refine ⟨7194151503632394448446097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38368808019372770391712517 7194151503632394448446097)
      ·
        refine ⟨5395613627724295836334573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7194151503632394448446097 5395613627724295836334573)
        ·
          refine ⟨2023355110396610938625465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5395613627724295836334573 2023355110396610938625465)
          ·
            refine ⟨1517516332797458203969099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023355110396610938625465 1517516332797458203969099)
            ·
              refine ⟨2276274499196187305953649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517516332797458203969099 2276274499196187305953649)
              ·
                refine ⟨1707205874397140479465237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276274499196187305953649 1707205874397140479465237)
                ·
                  refine ⟨80025275362365959974933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1707205874397140479465237 80025275362365959974933)
                  ·
                    rfl

theorem cell22_701319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_701319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701319 prefixEnd_701319 := by exact prefixLift 701319
  have htrace : WordTrace (prefixWord ++ tailWord_701319) baseStart_701319 baseEnd_701319 := by
    simpa [prefixWord, tailWord_701319, baseEnd_701319] using wordTrace_append hprefix tailTrace_701319
  have hstable : (prefixWord ++ tailWord_701319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701319).length < 2 ^ (prefixWord ++ tailWord_701319).sum := by decide
  have hdescent : baseEnd_701319 < baseStart_701319 := by decide
  rcases family_descends (prefixWord ++ tailWord_701319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701368 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_701368 : Nat := 118140960795 + 701368 * 2 ^ 59
def prefixEnd_701368 : Nat := 4983230072969 + 3 ^ 40 * 701368 * 2
def baseEnd_701368 : Nat := 240092599788478085449649

theorem tailTrace_701368 : CollatzResearch.WordTrace tailWord_701368 prefixEnd_701368 240092599788478085449649 := by
  unfold tailWord_701368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790496261535497481504379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17053995015380663308672505 12790496261535497481504379)
  ·
    refine ⟨19185744392303246222256569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12790496261535497481504379 19185744392303246222256569)
    ·
      refine ⟨14389308294227434666692427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19185744392303246222256569 14389308294227434666692427)
      ·
        refine ⟨21583962441341152000038641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14389308294227434666692427 21583962441341152000038641)
        ·
          refine ⟨16187971831005864000028981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21583962441341152000038641 16187971831005864000028981)
          ·
            refine ⟨1517622359156799750002717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16187971831005864000028981 1517622359156799750002717)
            ·
              refine ⟨569108384683799906251019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1517622359156799750002717 569108384683799906251019)
              ·
                refine ⟨853662577025699859376529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569108384683799906251019 853662577025699859376529)
                ·
                  refine ⟨640246932769274894532397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853662577025699859376529 640246932769274894532397)
                  ·
                    refine ⟨240092599788478085449649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 640246932769274894532397 240092599788478085449649)
                    ·
                      rfl

theorem cell22_701368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_701368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701368 prefixEnd_701368 := by exact prefixLift 701368
  have htrace : WordTrace (prefixWord ++ tailWord_701368) baseStart_701368 baseEnd_701368 := by
    simpa [prefixWord, tailWord_701368, baseEnd_701368] using wordTrace_append hprefix tailTrace_701368
  have hstable : (prefixWord ++ tailWord_701368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701368).length < 2 ^ (prefixWord ++ tailWord_701368).sum := by decide
  have hdescent : baseEnd_701368 < baseStart_701368 := by decide
  rcases family_descends (prefixWord ++ tailWord_701368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701409 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 5]
def baseStart_701409 : Nat := 118140960795 + 701409 * 2 ^ 59
def prefixEnd_701409 : Nat := 4983230072969 + 3 ^ 40 * 701409 * 2
def baseEnd_701409 : Nat := 80035544975455881724841

theorem tailTrace_701409 : CollatzResearch.WordTrace tailWord_701409 prefixEnd_701409 80035544975455881724841 := by
  unfold tailWord_701409
  simp only [CollatzResearch.WordTrace]
  refine ⟨25582487915922458965251281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17054991943948305976834187 25582487915922458965251281)
  ·
    refine ⟨19186865936941844223938461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25582487915922458965251281 19186865936941844223938461)
    ·
      refine ⟨7195074726353191583976923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19186865936941844223938461 7195074726353191583976923)
      ·
        refine ⟨10792612089529787375965385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7195074726353191583976923 10792612089529787375965385)
        ·
          refine ⟨8094459067147340531974039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10792612089529787375965385 8094459067147340531974039)
          ·
            refine ⟨12141688600721010797961059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8094459067147340531974039 12141688600721010797961059)
            ·
              refine ⟨18212532901081516196941589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12141688600721010797961059 18212532901081516196941589)
              ·
                refine ⟨853712479738196071731637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18212532901081516196941589 853712479738196071731637)
                ·
                  refine ⟨80035544975455881724841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 853712479738196071731637 80035544975455881724841)
                  ·
                    rfl

theorem cell22_701409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_701409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701409 prefixEnd_701409 := by exact prefixLift 701409
  have htrace : WordTrace (prefixWord ++ tailWord_701409) baseStart_701409 baseEnd_701409 := by
    simpa [prefixWord, tailWord_701409, baseEnd_701409] using wordTrace_append hprefix tailTrace_701409
  have hstable : (prefixWord ++ tailWord_701409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701409).length < 2 ^ (prefixWord ++ tailWord_701409).sum := by decide
  have hdescent : baseEnd_701409 < baseStart_701409 := by decide
  rcases family_descends (prefixWord ++ tailWord_701409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701484 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_701484 : Nat := 118140960795 + 701484 * 2 ^ 59
def prefixEnd_701484 : Nat := 4983230072969 + 3 ^ 40 * 701484 * 2
def baseEnd_701484 : Nat := 240132308959092449549293

theorem tailTrace_701484 : CollatzResearch.WordTrace tailWord_701484 prefixEnd_701484 240132308959092449549293 := by
  unfold tailWord_701484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792611695325373387115753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17056815593767164516154337 12792611695325373387115753)
  ·
    refine ⟨9594458771494030040336815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12792611695325373387115753 9594458771494030040336815)
    ·
      refine ⟨14391688157241045060505223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9594458771494030040336815 14391688157241045060505223)
      ·
        refine ⟨21587532235861567590757835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391688157241045060505223 21587532235861567590757835)
        ·
          refine ⟨32381298353792351386136753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21587532235861567590757835 32381298353792351386136753)
          ·
            refine ⟨24285973765344263539602565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32381298353792351386136753 24285973765344263539602565)
            ·
              refine ⟨4553620081002049413675481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24285973765344263539602565 4553620081002049413675481)
              ·
                refine ⟨3415215060751537060256611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553620081002049413675481 3415215060751537060256611)
                ·
                  refine ⟨5122822591127305590384917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415215060751537060256611 5122822591127305590384917)
                  ·
                    refine ⟨240132308959092449549293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5122822591127305590384917 240132308959092449549293)
                    ·
                      rfl

theorem cell22_701484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_701484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701484 prefixEnd_701484 := by exact prefixLift 701484
  have htrace : WordTrace (prefixWord ++ tailWord_701484) baseStart_701484 baseEnd_701484 := by
    simpa [prefixWord, tailWord_701484, baseEnd_701484] using wordTrace_append hprefix tailTrace_701484
  have hstable : (prefixWord ++ tailWord_701484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701484).length < 2 ^ (prefixWord ++ tailWord_701484).sum := by decide
  have hdescent : baseEnd_701484 < baseStart_701484 := by decide
  rcases family_descends (prefixWord ++ tailWord_701484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701501 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_701501 : Nat := 118140960795 + 701501 * 2 ^ 59
def prefixEnd_701501 : Nat := 4983230072969 + 3 ^ 40 * 701501 * 2
def baseEnd_701501 : Nat := 240138128406510071874241

theorem tailTrace_701501 : CollatzResearch.WordTrace tailWord_701501 prefixEnd_701501 240138128406510071874241 := by
  unfold tailWord_701501
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585843431589158677600357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17057228954392772451733571 25585843431589158677600357)
  ·
    refine ⟨4797345643422967252050067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25585843431589158677600357 4797345643422967252050067)
    ·
      refine ⟨7196018465134450878075101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797345643422967252050067 7196018465134450878075101)
      ·
        refine ⟨2698506924425419079278163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7196018465134450878075101 2698506924425419079278163)
        ·
          refine ⟨4047760386638128618917245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698506924425419079278163 4047760386638128618917245)
          ·
            refine ⟨1517910144989298232093967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4047760386638128618917245 1517910144989298232093967)
            ·
              refine ⟨2276865217483947348140951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517910144989298232093967 2276865217483947348140951)
              ·
                refine ⟨3415297826225921022211427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276865217483947348140951 3415297826225921022211427)
                ·
                  refine ⟨5122946739338881533317141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415297826225921022211427 5122946739338881533317141)
                  ·
                    refine ⟨240138128406510071874241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5122946739338881533317141 240138128406510071874241)
                    ·
                      rfl

theorem cell22_701501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_701501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_701501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_701501 prefixEnd_701501 := by exact prefixLift 701501
  have htrace : WordTrace (prefixWord ++ tailWord_701501) baseStart_701501 baseEnd_701501 := by
    simpa [prefixWord, tailWord_701501, baseEnd_701501] using wordTrace_append hprefix tailTrace_701501
  have hstable : (prefixWord ++ tailWord_701501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701501).length < 2 ^ (prefixWord ++ tailWord_701501).sum := by decide
  have hdescent : baseEnd_701501 < baseStart_701501 := by decide
  rcases family_descends (prefixWord ++ tailWord_701501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
