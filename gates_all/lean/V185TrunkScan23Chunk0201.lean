import V185TrunkScan23Chunk0200

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1189761 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1189761 : Nat := 118140960795 + 1189761 * 2 ^ 59
def prefixEnd_1189761 : Nat := 4983230072969 + 3 ^ 40 * 1189761 * 2
def baseEnd_1189761 : Nat := 610919256974024788315895

theorem tailTrace_1189761 : CollatzResearch.WordTrace tailWord_1189761 prefixEnd_1189761 610919256974024788315895 := by
  unfold tailWord_1189761
  simp only [CollatzResearch.WordTrace]
  refine ⟨43394148642706566846729137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28929432428471044564486091 43394148642706566846729137)
  ·
    refine ⟨32545611482029925135046853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43394148642706566846729137 32545611482029925135046853)
    ·
      refine ⟨6102302152880610962821285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32545611482029925135046853 6102302152880610962821285)
      ·
        refine ⟨1144181653665114555528991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6102302152880610962821285 1144181653665114555528991)
        ·
          refine ⟨1716272480497671833293487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144181653665114555528991 1716272480497671833293487)
          ·
            refine ⟨2574408720746507749940231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716272480497671833293487 2574408720746507749940231)
            ·
              refine ⟨3861613081119761624910347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574408720746507749940231 3861613081119761624910347)
              ·
                refine ⟨5792419621679642437365521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861613081119761624910347 5792419621679642437365521)
                ·
                  refine ⟨4344314716259731828024141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5792419621679642437365521 4344314716259731828024141)
                  ·
                    refine ⟨1629118018597399435509053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4344314716259731828024141 1629118018597399435509053)
                    ·
                      refine ⟨610919256974024788315895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1629118018597399435509053 610919256974024788315895)
                      ·
                        rfl

theorem cell23_1189761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1189761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189761 prefixEnd_1189761 := by exact prefixLift 1189761
  have htrace : WordTrace (prefixWord ++ tailWord_1189761) baseStart_1189761 baseEnd_1189761 := by
    simpa [prefixWord, tailWord_1189761, baseEnd_1189761] using wordTrace_append hprefix tailTrace_1189761
  have hstable : (prefixWord ++ tailWord_1189761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189761).length < 2 ^ (prefixWord ++ tailWord_1189761).sum := by decide
  have hdescent : baseEnd_1189761 < baseStart_1189761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189777 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_1189777 : Nat := 118140960795 + 1189777 * 2 ^ 59
def prefixEnd_1189777 : Nat := 4983230072969 + 3 ^ 40 * 1189777 * 2
def baseEnd_1189777 : Nat := 203642490888165575238607

theorem tailTrace_1189777 : CollatzResearch.WordTrace tailWord_1189777 prefixEnd_1189777 203642490888165575238607 := by
  unfold tailWord_1189777
  simp only [CollatzResearch.WordTrace]
  refine ⟨43394732210648601579311585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28929821473765734386207723 43394732210648601579311585)
  ·
    refine ⟨32546049157986451184483689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43394732210648601579311585 32546049157986451184483689)
    ·
      refine ⟨24409536868489838388362767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32546049157986451184483689 24409536868489838388362767)
      ·
        refine ⟨36614305302734757582544151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24409536868489838388362767 36614305302734757582544151)
        ·
          refine ⟨54921457954102136373816227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36614305302734757582544151 54921457954102136373816227)
          ·
            refine ⟨82382186931153204560724341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54921457954102136373816227 82382186931153204560724341)
            ·
              refine ⟨7723330024795612927567907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82382186931153204560724341 7723330024795612927567907)
              ·
                refine ⟨11584995037193419391351861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7723330024795612927567907 11584995037193419391351861)
                ·
                  refine ⟨1086093284736883067939237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11584995037193419391351861 1086093284736883067939237)
                  ·
                    refine ⟨203642490888165575238607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086093284736883067939237 203642490888165575238607)
                    ·
                      rfl

theorem cell23_1189777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_1189777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189777 prefixEnd_1189777 := by exact prefixLift 1189777
  have htrace : WordTrace (prefixWord ++ tailWord_1189777) baseStart_1189777 baseEnd_1189777 := by
    simpa [prefixWord, tailWord_1189777, baseEnd_1189777] using wordTrace_append hprefix tailTrace_1189777
  have hstable : (prefixWord ++ tailWord_1189777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189777).length < 2 ^ (prefixWord ++ tailWord_1189777).sum := by decide
  have hdescent : baseEnd_1189777 < baseStart_1189777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189824 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 6]
def baseStart_1189824 : Nat := 118140960795 + 1189824 * 2 ^ 59
def prefixEnd_1189824 : Nat := 4983230072969 + 3 ^ 40 * 1189824 * 2
def baseEnd_1189824 : Nat := 67883511806139782425345

theorem tailTrace_1189824 : CollatzResearch.WordTrace tailWord_1189824 prefixEnd_1189824 67883511806139782425345 := by
  unfold tailWord_1189824
  simp only [CollatzResearch.WordTrace]
  refine ⟨21698223220739164303136263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28930964294318885737515017 21698223220739164303136263)
  ·
    refine ⟨32547334831108746454704395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21698223220739164303136263 32547334831108746454704395)
    ·
      refine ⟨48821002246663119682056593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32547334831108746454704395 48821002246663119682056593)
      ·
        refine ⟨36615751684997339761542445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48821002246663119682056593 36615751684997339761542445)
        ·
          refine ⟨13730906881874002410578417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36615751684997339761542445 13730906881874002410578417)
          ·
            refine ⟨10298180161405501807933813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13730906881874002410578417 10298180161405501807933813)
            ·
              refine ⟨965454390131765794493795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10298180161405501807933813 965454390131765794493795)
              ·
                refine ⟨1448181585197648691740693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965454390131765794493795 1448181585197648691740693)
                ·
                  refine ⟨67883511806139782425345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1448181585197648691740693 67883511806139782425345)
                  ·
                    rfl

theorem cell23_1189824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 6].length) (baseStart_1189824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189824 prefixEnd_1189824 := by exact prefixLift 1189824
  have htrace : WordTrace (prefixWord ++ tailWord_1189824) baseStart_1189824 baseEnd_1189824 := by
    simpa [prefixWord, tailWord_1189824, baseEnd_1189824] using wordTrace_append hprefix tailTrace_1189824
  have hstable : (prefixWord ++ tailWord_1189824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189824).length < 2 ^ (prefixWord ++ tailWord_1189824).sum := by decide
  have hdescent : baseEnd_1189824 < baseStart_1189824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189887 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1189887 : Nat := 118140960795 + 1189887 * 2 ^ 59
def prefixEnd_1189887 : Nat := 4983230072969 + 3 ^ 40 * 1189887 * 2
def baseEnd_1189887 : Nat := 610983955536491295340315

theorem tailTrace_1189887 : CollatzResearch.WordTrace tailWord_1189887 prefixEnd_1189887 610983955536491295340315 := by
  unfold tailWord_1189887
  simp only [CollatzResearch.WordTrace]
  refine ⟨43398744240250090365815915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28932496160166726910543943 43398744240250090365815915)
  ·
    refine ⟨65098116360375135548723873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43398744240250090365815915 65098116360375135548723873)
    ·
      refine ⟨48823587270281351661542905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65098116360375135548723873 48823587270281351661542905)
      ·
        refine ⟨36617690452711013746157179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48823587270281351661542905 36617690452711013746157179)
        ·
          refine ⟨54926535679066520619235769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36617690452711013746157179 54926535679066520619235769)
          ·
            refine ⟨41194901759299890464426827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54926535679066520619235769 41194901759299890464426827)
            ·
              refine ⟨61792352638949835696640241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41194901759299890464426827 61792352638949835696640241)
              ·
                refine ⟨46344264479212376772480181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61792352638949835696640241 46344264479212376772480181)
                ·
                  refine ⟨4344774794926160322420017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46344264479212376772480181 4344774794926160322420017)
                  ·
                    refine ⟨3258581096194620241815013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4344774794926160322420017 3258581096194620241815013)
                    ·
                      refine ⟨610983955536491295340315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3258581096194620241815013 610983955536491295340315)
                      ·
                        rfl

theorem cell23_1189887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1189887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189887 prefixEnd_1189887 := by exact prefixLift 1189887
  have htrace : WordTrace (prefixWord ++ tailWord_1189887) baseStart_1189887 baseEnd_1189887 := by
    simpa [prefixWord, tailWord_1189887, baseEnd_1189887] using wordTrace_append hprefix tailTrace_1189887
  have hstable : (prefixWord ++ tailWord_1189887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189887).length < 2 ^ (prefixWord ++ tailWord_1189887).sum := by decide
  have hdescent : baseEnd_1189887 < baseStart_1189887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189891 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 3, 2, 2]
def baseStart_1189891 : Nat := 118140960795 + 1189891 * 2 ^ 59
def prefixEnd_1189891 : Nat := 4983230072969 + 3 ^ 40 * 1189891 * 2
def baseEnd_1189891 : Nat := 610986009459109279690297

theorem tailTrace_1189891 : CollatzResearch.WordTrace tailWord_1189891 prefixEnd_1189891 610986009459109279690297 := by
  unfold tailWord_1189891
  simp only [CollatzResearch.WordTrace]
  refine ⟨43398890132235599048961527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28932593421490399365974351 43398890132235599048961527)
  ·
    refine ⟨65098335198353398573442291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43398890132235599048961527 65098335198353398573442291)
    ·
      refine ⟨97647502797530097860163437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65098335198353398573442291 97647502797530097860163437)
      ·
        refine ⟨36617813549073786697561289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97647502797530097860163437 36617813549073786697561289)
        ·
          refine ⟨27463360161805340023170967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36617813549073786697561289 27463360161805340023170967)
          ·
            refine ⟨41195040242708010034756451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27463360161805340023170967 41195040242708010034756451)
            ·
              refine ⟨61792560364062015052134677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41195040242708010034756451 61792560364062015052134677)
              ·
                refine ⟨2896526267065406955568813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61792560364062015052134677 2896526267065406955568813)
                ·
                  refine ⟨1086197350149527608338305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2896526267065406955568813 1086197350149527608338305)
                  ·
                    refine ⟨814648012612145706253729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086197350149527608338305 814648012612145706253729)
                    ·
                      refine ⟨610986009459109279690297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814648012612145706253729 610986009459109279690297)
                      ·
                        rfl

theorem cell23_1189891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_1189891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189891 prefixEnd_1189891 := by exact prefixLift 1189891
  have htrace : WordTrace (prefixWord ++ tailWord_1189891) baseStart_1189891 baseEnd_1189891 := by
    simpa [prefixWord, tailWord_1189891, baseEnd_1189891] using wordTrace_append hprefix tailTrace_1189891
  have hstable : (prefixWord ++ tailWord_1189891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189891).length < 2 ^ (prefixWord ++ tailWord_1189891).sum := by decide
  have hdescent : baseEnd_1189891 < baseStart_1189891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189925 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 1, 2, 2]
def baseStart_1189925 : Nat := 118140960795 + 1189925 * 2 ^ 59
def prefixEnd_1189925 : Nat := 4983230072969 + 3 ^ 40 * 1189925 * 2
def baseEnd_1189925 : Nat := 611003467801362146665141

theorem tailTrace_1189925 : CollatzResearch.WordTrace tailWord_1189925 prefixEnd_1189925 611003467801362146665141 := by
  unfold tailWord_1189925
  simp only [CollatzResearch.WordTrace]
  refine ⟨43400130214112422855699229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28933420142741615237132819 43400130214112422855699229)
  ·
    refine ⟨16275048830292158570887211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43400130214112422855699229 16275048830292158570887211)
    ·
      refine ⟨24412573245438237856330817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275048830292158570887211 24412573245438237856330817)
      ·
        refine ⟨18309429934078678392248113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24412573245438237856330817 18309429934078678392248113)
        ·
          refine ⟨13732072450559008794186085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18309429934078678392248113 13732072450559008794186085)
          ·
            refine ⟨2574763584479814148909891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13732072450559008794186085 2574763584479814148909891)
            ·
              refine ⟨3862145376719721223364837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574763584479814148909891 3862145376719721223364837)
              ·
                refine ⟨724152258134947729380907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3862145376719721223364837 724152258134947729380907)
                ·
                  refine ⟨1086228387202421594071361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724152258134947729380907 1086228387202421594071361)
                  ·
                    refine ⟨814671290401816195553521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086228387202421594071361 814671290401816195553521)
                    ·
                      refine ⟨611003467801362146665141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814671290401816195553521 611003467801362146665141)
                      ·
                        rfl

theorem cell23_1189925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_1189925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189925 prefixEnd_1189925 := by exact prefixLift 1189925
  have htrace : WordTrace (prefixWord ++ tailWord_1189925) baseStart_1189925 baseEnd_1189925 := by
    simpa [prefixWord, tailWord_1189925, baseEnd_1189925] using wordTrace_append hprefix tailTrace_1189925
  have hstable : (prefixWord ++ tailWord_1189925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189925).length < 2 ^ (prefixWord ++ tailWord_1189925).sum := by decide
  have hdescent : baseEnd_1189925 < baseStart_1189925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189951 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 3, 3, 2]
def baseStart_1189951 : Nat := 118140960795 + 1189951 * 2 ^ 59
def prefixEnd_1189951 : Nat := 4983230072969 + 3 ^ 40 * 1189951 * 2
def baseEnd_1189951 : Nat := 611016818298379044940021

theorem tailTrace_1189951 : CollatzResearch.WordTrace tailWord_1189951 prefixEnd_1189951 611016818298379044940021 := by
  unfold tailWord_1189951
  simp only [CollatzResearch.WordTrace]
  refine ⟨43401078512018229296145707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28934052341345486197430471 43401078512018229296145707)
  ·
    refine ⟨65101617768027343944218561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43401078512018229296145707 65101617768027343944218561)
    ·
      refine ⟨48826213326020507958163921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65101617768027343944218561 48826213326020507958163921)
      ·
        refine ⟨36619659994515380968622941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48826213326020507958163921 36619659994515380968622941)
        ·
          refine ⟨13732372497943267863233603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36619659994515380968622941 13732372497943267863233603)
          ·
            refine ⟨20598558746914901794850405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13732372497943267863233603 20598558746914901794850405)
            ·
              refine ⟨3862229765046544086534451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20598558746914901794850405 3862229765046544086534451)
              ·
                refine ⟨5793344647569816129801677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862229765046544086534451 5793344647569816129801677)
                ·
                  refine ⟨2172504242838681048675629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5793344647569816129801677 2172504242838681048675629)
                  ·
                    refine ⟨814689091064505393253361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2172504242838681048675629 814689091064505393253361)
                    ·
                      refine ⟨611016818298379044940021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 814689091064505393253361 611016818298379044940021)
                      ·
                        rfl

theorem cell23_1189951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_1189951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189951 prefixEnd_1189951 := by exact prefixLift 1189951
  have htrace : WordTrace (prefixWord ++ tailWord_1189951) baseStart_1189951 baseEnd_1189951 := by
    simpa [prefixWord, tailWord_1189951, baseEnd_1189951] using wordTrace_append hprefix tailTrace_1189951
  have hstable : (prefixWord ++ tailWord_1189951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189951).length < 2 ^ (prefixWord ++ tailWord_1189951).sum := by decide
  have hdescent : baseEnd_1189951 < baseStart_1189951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189957 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_1189957 : Nat := 118140960795 + 1189957 * 2 ^ 59
def prefixEnd_1189957 : Nat := 4983230072969 + 3 ^ 40 * 1189957 * 2
def baseEnd_1189957 : Nat := 203673299727435340488331

theorem tailTrace_1189957 : CollatzResearch.WordTrace tailWord_1189957 prefixEnd_1189957 203673299727435340488331 := by
  unfold tailWord_1189957
  simp only [CollatzResearch.WordTrace]
  refine ⟨43401297349996492320864125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28934198233330994880576083 43401297349996492320864125)
  ·
    refine ⟨16275486506248684620324047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43401297349996492320864125 16275486506248684620324047)
    ·
      refine ⟨24413229759373026930486071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16275486506248684620324047 24413229759373026930486071)
      ·
        refine ⟨36619844639059540395729107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24413229759373026930486071 36619844639059540395729107)
        ·
          refine ⟨54929766958589310593593661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36619844639059540395729107 54929766958589310593593661)
          ·
            refine ⟨20598662609470991472597623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54929766958589310593593661 20598662609470991472597623)
            ·
              refine ⟨30897993914206487208896435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20598662609470991472597623 30897993914206487208896435)
              ·
                refine ⟨46346990871309730813344653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30897993914206487208896435 46346990871309730813344653)
                ·
                  refine ⟨17380121576741149055004245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46346990871309730813344653 17380121576741149055004245)
                  ·
                    refine ⟨203673299727435340488331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17380121576741149055004245 203673299727435340488331)
                    ·
                      rfl

theorem cell23_1189957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_1189957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189957 prefixEnd_1189957 := by exact prefixLift 1189957
  have htrace : WordTrace (prefixWord ++ tailWord_1189957) baseStart_1189957 baseEnd_1189957 := by
    simpa [prefixWord, tailWord_1189957, baseEnd_1189957] using wordTrace_append hprefix tailTrace_1189957
  have hstable : (prefixWord ++ tailWord_1189957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189957).length < 2 ^ (prefixWord ++ tailWord_1189957).sum := by decide
  have hdescent : baseEnd_1189957 < baseStart_1189957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189958 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1189958 : Nat := 118140960795 + 1189958 * 2 ^ 59
def prefixEnd_1189958 : Nat := 4983230072969 + 3 ^ 40 * 1189958 * 2
def baseEnd_1189958 : Nat := 611020412662960517552489

theorem tailTrace_1189958 : CollatzResearch.WordTrace tailWord_1189958 prefixEnd_1189958 611020412662960517552489 := by
  unfold tailWord_1189958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356291681968527171614079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28934222548661912994433685 1356291681968527171614079)
  ·
    refine ⟨2034437522952790757421119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1356291681968527171614079 2034437522952790757421119)
    ·
      refine ⟨3051656284429186136131679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034437522952790757421119 3051656284429186136131679)
      ·
        refine ⟨4577484426643779204197519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051656284429186136131679 4577484426643779204197519)
        ·
          refine ⟨6866226639965668806296279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577484426643779204197519 6866226639965668806296279)
          ·
            refine ⟨10299339959948503209444419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6866226639965668806296279 10299339959948503209444419)
            ·
              refine ⟨15449009939922754814166629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10299339959948503209444419 15449009939922754814166629)
              ·
                refine ⟨2896689363735516527656243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15449009939922754814166629 2896689363735516527656243)
                ·
                  refine ⟨4345034045603274791484365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2896689363735516527656243 4345034045603274791484365)
                  ·
                    refine ⟨1629387767101228046806637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4345034045603274791484365 1629387767101228046806637)
                    ·
                      refine ⟨611020412662960517552489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1629387767101228046806637 611020412662960517552489)
                      ·
                        rfl

theorem cell23_1189958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1189958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1189958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1189958 prefixEnd_1189958 := by exact prefixLift 1189958
  have htrace : WordTrace (prefixWord ++ tailWord_1189958) baseStart_1189958 baseEnd_1189958 := by
    simpa [prefixWord, tailWord_1189958, baseEnd_1189958] using wordTrace_append hprefix tailTrace_1189958
  have hstable : (prefixWord ++ tailWord_1189958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189958).length < 2 ^ (prefixWord ++ tailWord_1189958).sum := by decide
  have hdescent : baseEnd_1189958 < baseStart_1189958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190071 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_1190071 : Nat := 118140960795 + 1190071 * 2 ^ 59
def prefixEnd_1190071 : Nat := 4983230072969 + 3 ^ 40 * 1190071 * 2
def baseEnd_1190071 : Nat := 611078435976918575439469

theorem tailTrace_1190071 : CollatzResearch.WordTrace tailWord_1190071 prefixEnd_1190071 611078435976918575439469 := by
  unfold tailWord_1190071
  simp only [CollatzResearch.WordTrace]
  refine ⟨43405455271583489790514067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28936970181055659860342711 43405455271583489790514067)
  ·
    refine ⟨65108182907375234685771101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43405455271583489790514067 65108182907375234685771101)
    ·
      refine ⟨24415568590265713007164163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65108182907375234685771101 24415568590265713007164163)
      ·
        refine ⟨36623352885398569510746245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24415568590265713007164163 36623352885398569510746245)
        ·
          refine ⟨6866878666012231783264921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36623352885398569510746245 6866878666012231783264921)
          ·
            refine ⟨5150158999509173837448691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6866878666012231783264921 5150158999509173837448691)
            ·
              refine ⟨7725238499263760756173037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150158999509173837448691 7725238499263760756173037)
              ·
                refine ⟨2896964437223910283564889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7725238499263760756173037 2896964437223910283564889)
                ·
                  refine ⟨2172723327917932712673667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896964437223910283564889 2172723327917932712673667)
                  ·
                    refine ⟨3259084991876899069010501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2172723327917932712673667 3259084991876899069010501)
                    ·
                      refine ⟨611078435976918575439469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3259084991876899069010501 611078435976918575439469)
                      ·
                        rfl

theorem cell23_1190071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_1190071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190071 prefixEnd_1190071 := by exact prefixLift 1190071
  have htrace : WordTrace (prefixWord ++ tailWord_1190071) baseStart_1190071 baseEnd_1190071 := by
    simpa [prefixWord, tailWord_1190071, baseEnd_1190071] using wordTrace_append hprefix tailTrace_1190071
  have hstable : (prefixWord ++ tailWord_1190071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190071).length < 2 ^ (prefixWord ++ tailWord_1190071).sum := by decide
  have hdescent : baseEnd_1190071 < baseStart_1190071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190091 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3]
def baseStart_1190091 : Nat := 118140960795 + 1190091 * 2 ^ 59
def prefixEnd_1190091 : Nat := 4983230072969 + 3 ^ 40 * 1190091 * 2
def baseEnd_1190091 : Nat := 611088705590008497189377

theorem tailTrace_1190091 : CollatzResearch.WordTrace tailWord_1190091 prefixEnd_1190091 611088705590008497189377 := by
  unfold tailWord_1190091
  simp only [CollatzResearch.WordTrace]
  refine ⟨43406184731511033206242127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28937456487674022137494751 43406184731511033206242127)
  ·
    refine ⟨65109277097266549809363191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43406184731511033206242127 65109277097266549809363191)
    ·
      refine ⟨97663915645899824714044787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65109277097266549809363191 97663915645899824714044787)
      ·
        refine ⟨146495873468849737071067181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97663915645899824714044787 146495873468849737071067181)
        ·
          refine ⟨54935952550818651401650193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146495873468849737071067181 54935952550818651401650193)
          ·
            refine ⟨41201964413113988551237645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54935952550818651401650193 41201964413113988551237645)
            ·
              refine ⟨15450736654917745706714117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41201964413113988551237645 15450736654917745706714117)
              ·
                refine ⟨2897013122797077320008897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15450736654917745706714117 2897013122797077320008897)
                ·
                  refine ⟨2172759842097807990006673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897013122797077320008897 2172759842097807990006673)
                  ·
                    refine ⟨1629569881573355992505005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2172759842097807990006673 1629569881573355992505005)
                    ·
                      refine ⟨611088705590008497189377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1629569881573355992505005 611088705590008497189377)
                      ·
                        rfl

theorem cell23_1190091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 3].length) (baseStart_1190091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190091 prefixEnd_1190091 := by exact prefixLift 1190091
  have htrace : WordTrace (prefixWord ++ tailWord_1190091) baseStart_1190091 baseEnd_1190091 := by
    simpa [prefixWord, tailWord_1190091, baseEnd_1190091] using wordTrace_append hprefix tailTrace_1190091
  have hstable : (prefixWord ++ tailWord_1190091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190091).length < 2 ^ (prefixWord ++ tailWord_1190091).sum := by decide
  have hdescent : baseEnd_1190091 < baseStart_1190091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190115 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 3, 4]
def baseStart_1190115 : Nat := 118140960795 + 1190115 * 2 ^ 59
def prefixEnd_1190115 : Nat := 4983230072969 + 3 ^ 40 * 1190115 * 2
def baseEnd_1190115 : Nat := 203700343041905467763089

theorem tailTrace_1190115 : CollatzResearch.WordTrace tailWord_1190115 prefixEnd_1190115 203700343041905467763089 := by
  unfold tailWord_1190115
  simp only [CollatzResearch.WordTrace]
  refine ⟨43407060083424085305115799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28938040055616056870077199 43407060083424085305115799)
  ·
    refine ⟨65110590125136127957673699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43407060083424085305115799 65110590125136127957673699)
    ·
      refine ⟨97665885187704191936510549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65110590125136127957673699 97665885187704191936510549)
      ·
        refine ⟨1144522092043408499255983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 97665885187704191936510549 1144522092043408499255983)
        ·
          refine ⟨1716783138065112748883975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144522092043408499255983 1716783138065112748883975)
          ·
            refine ⟨2575174707097669123325963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716783138065112748883975 2575174707097669123325963)
            ·
              refine ⟨3862762060646503684988945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575174707097669123325963 3862762060646503684988945)
              ·
                refine ⟨2897071545484877763741709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862762060646503684988945 2897071545484877763741709)
                ·
                  refine ⟨1086401829556829161403141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2897071545484877763741709 1086401829556829161403141)
                  ·
                    refine ⟨203700343041905467763089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086401829556829161403141 203700343041905467763089)
                    ·
                      rfl

theorem cell23_1190115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 4].length) (baseStart_1190115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190115 prefixEnd_1190115 := by exact prefixLift 1190115
  have htrace : WordTrace (prefixWord ++ tailWord_1190115) baseStart_1190115 baseEnd_1190115 := by
    simpa [prefixWord, tailWord_1190115, baseEnd_1190115] using wordTrace_append hprefix tailTrace_1190115
  have hstable : (prefixWord ++ tailWord_1190115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190115).length < 2 ^ (prefixWord ++ tailWord_1190115).sum := by decide
  have hdescent : baseEnd_1190115 < baseStart_1190115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190155 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 1, 1, 3]
def baseStart_1190155 : Nat := 118140960795 + 1190155 * 2 ^ 59
def prefixEnd_1190155 : Nat := 4983230072969 + 3 ^ 40 * 1190155 * 2
def baseEnd_1190155 : Nat := 611121568351896246789083

theorem tailTrace_1190155 : CollatzResearch.WordTrace tailWord_1190155 prefixEnd_1190155 611121568351896246789083 := by
  unfold tailWord_1190155
  simp only [CollatzResearch.WordTrace]
  refine ⟨43408519003279172136571919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28939012668852781424381279 43408519003279172136571919)
  ·
    refine ⟨65112778504918758204857879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43408519003279172136571919 65112778504918758204857879)
    ·
      refine ⟨97669167757378137307286819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65112778504918758204857879 97669167757378137307286819)
      ·
        refine ⟨146503751636067205960930229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97669167757378137307286819 146503751636067205960930229)
        ·
          refine ⟨13734726715881300558837209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146503751636067205960930229 13734726715881300558837209)
          ·
            refine ⟨10301045036910975419127907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13734726715881300558837209 10301045036910975419127907)
            ·
              refine ⟨15451567555366463128691861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10301045036910975419127907 15451567555366463128691861)
              ·
                refine ⟨724292229157802959157431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15451567555366463128691861 724292229157802959157431)
                ·
                  refine ⟨1086438343736704438736147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724292229157802959157431 1086438343736704438736147)
                  ·
                    refine ⟨1629657515605056658104221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1086438343736704438736147 1629657515605056658104221)
                    ·
                      refine ⟨611121568351896246789083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1629657515605056658104221 611121568351896246789083)
                      ·
                        rfl

theorem cell23_1190155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 1, 3].length) (baseStart_1190155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190155 prefixEnd_1190155 := by exact prefixLift 1190155
  have htrace : WordTrace (prefixWord ++ tailWord_1190155) baseStart_1190155 baseEnd_1190155 := by
    simpa [prefixWord, tailWord_1190155, baseEnd_1190155] using wordTrace_append hprefix tailTrace_1190155
  have hstable : (prefixWord ++ tailWord_1190155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190155).length < 2 ^ (prefixWord ++ tailWord_1190155).sum := by decide
  have hdescent : baseEnd_1190155 < baseStart_1190155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190171 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 1, 6]
def baseStart_1190171 : Nat := 118140960795 + 1190171 * 2 ^ 59
def prefixEnd_1190171 : Nat := 4983230072969 + 3 ^ 40 * 1190171 * 2
def baseEnd_1190171 : Nat := 203709928014122728063003

theorem tailTrace_1190171 : CollatzResearch.WordTrace tailWord_1190171 prefixEnd_1190171 203709928014122728063003 := by
  unfold tailWord_1190171
  simp only [CollatzResearch.WordTrace]
  refine ⟨43409102571221206869154367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28939401714147471246102911 43409102571221206869154367)
  ·
    refine ⟨65113653856831810303731551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43409102571221206869154367 65113653856831810303731551)
    ·
      refine ⟨97670480785247715455597327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65113653856831810303731551 97670480785247715455597327)
      ·
        refine ⟨146505721177871573183395991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97670480785247715455597327 146505721177871573183395991)
        ·
          refine ⟨219758581766807359775093987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146505721177871573183395991 219758581766807359775093987)
          ·
            refine ⟨329637872650211039662640981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219758581766807359775093987 329637872650211039662640981)
            ·
              refine ⟨1931471910059830310523287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 329637872650211039662640981 1931471910059830310523287)
              ·
                refine ⟨2897207865089745465784931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931471910059830310523287 2897207865089745465784931)
                ·
                  refine ⟨4345811797634618198677397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897207865089745465784931 4345811797634618198677397)
                  ·
                    refine ⟨203709928014122728063003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4345811797634618198677397 203709928014122728063003)
                    ·
                      rfl

theorem cell23_1190171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 6].length) (baseStart_1190171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190171 prefixEnd_1190171 := by exact prefixLift 1190171
  have htrace : WordTrace (prefixWord ++ tailWord_1190171) baseStart_1190171 baseEnd_1190171 := by
    simpa [prefixWord, tailWord_1190171, baseEnd_1190171] using wordTrace_append hprefix tailTrace_1190171
  have hstable : (prefixWord ++ tailWord_1190171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190171).length < 2 ^ (prefixWord ++ tailWord_1190171).sum := by decide
  have hdescent : baseEnd_1190171 < baseStart_1190171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190183 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1190183 : Nat := 118140960795 + 1190183 * 2 ^ 59
def prefixEnd_1190183 : Nat := 4983230072969 + 3 ^ 40 * 1190183 * 2
def baseEnd_1190183 : Nat := 203711981936740712412985

theorem tailTrace_1190183 : CollatzResearch.WordTrace tailWord_1190183 prefixEnd_1190183 203711981936740712412985 := by
  unfold tailWord_1190183
  simp only [CollatzResearch.WordTrace]
  refine ⟨43409540247177732918591203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28939693498118488612394135 43409540247177732918591203)
  ·
    refine ⟨65114310370766599377886805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43409540247177732918591203 65114310370766599377886805)
    ·
      refine ⟨763058324657421086459611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 65114310370766599377886805 763058324657421086459611)
      ·
        refine ⟨1144587486986131629689417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763058324657421086459611 1144587486986131629689417)
        ·
          refine ⟨858440615239598722267063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1144587486986131629689417 858440615239598722267063)
          ·
            refine ⟨1287660922859398083400595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858440615239598722267063 1287660922859398083400595)
            ·
              refine ⟨1931491384289097125100893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287660922859398083400595 1931491384289097125100893)
              ·
                refine ⟨724309269108411421912835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1931491384289097125100893 724309269108411421912835)
                ·
                  refine ⟨1086463903662617132869253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724309269108411421912835 1086463903662617132869253)
                  ·
                    refine ⟨203711981936740712412985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086463903662617132869253 203711981936740712412985)
                    ·
                      rfl

theorem cell23_1190183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1190183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190183 prefixEnd_1190183 := by exact prefixLift 1190183
  have htrace : WordTrace (prefixWord ++ tailWord_1190183) baseStart_1190183 baseEnd_1190183 := by
    simpa [prefixWord, tailWord_1190183, baseEnd_1190183] using wordTrace_append hprefix tailTrace_1190183
  have hstable : (prefixWord ++ tailWord_1190183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190183).length < 2 ^ (prefixWord ++ tailWord_1190183).sum := by decide
  have hdescent : baseEnd_1190183 < baseStart_1190183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190191 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_1190191 : Nat := 118140960795 + 1190191 * 2 ^ 59
def prefixEnd_1190191 : Nat := 4983230072969 + 3 ^ 40 * 1190191 * 2
def baseEnd_1190191 : Nat := 611140053655458105938917

theorem tailTrace_1190191 : CollatzResearch.WordTrace tailWord_1190191 prefixEnd_1190191 611140053655458105938917 := by
  unfold tailWord_1190191
  simp only [CollatzResearch.WordTrace]
  refine ⟨43409832031148750284882427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28939888020765833523254951 43409832031148750284882427)
  ·
    refine ⟨65114748046723125427323641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43409832031148750284882427 65114748046723125427323641)
    ·
      refine ⟨48836061035042344070492731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65114748046723125427323641 48836061035042344070492731)
      ·
        refine ⟨73254091552563516105739097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48836061035042344070492731 73254091552563516105739097)
        ·
          refine ⟨54940568664422637079304323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73254091552563516105739097 54940568664422637079304323)
          ·
            refine ⟨82410852996633955618956485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54940568664422637079304323 82410852996633955618956485)
            ·
              refine ⟨15452034936868866678554341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82410852996633955618956485 15452034936868866678554341)
              ·
                refine ⟨2897256550662912502228939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15452034936868866678554341 2897256550662912502228939)
                ·
                  refine ⟨4345884825994368753343409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897256550662912502228939 4345884825994368753343409)
                  ·
                    refine ⟨3259413619495776565007557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4345884825994368753343409 3259413619495776565007557)
                    ·
                      refine ⟨611140053655458105938917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3259413619495776565007557 611140053655458105938917)
                      ·
                        rfl

theorem cell23_1190191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_1190191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190191 prefixEnd_1190191 := by exact prefixLift 1190191
  have htrace : WordTrace (prefixWord ++ tailWord_1190191) baseStart_1190191 baseEnd_1190191 := by
    simpa [prefixWord, tailWord_1190191, baseEnd_1190191] using wordTrace_append hprefix tailTrace_1190191
  have hstable : (prefixWord ++ tailWord_1190191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190191).length < 2 ^ (prefixWord ++ tailWord_1190191).sum := by decide
  have hdescent : baseEnd_1190191 < baseStart_1190191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190201 : List Nat := [1, 2, 1, 6, 1, 1, 11]
def baseStart_1190201 : Nat := 118140960795 + 1190201 * 2 ^ 59
def prefixEnd_1190201 : Nat := 4983230072969 + 3 ^ 40 * 1190201 * 2
def baseEnd_1190201 : Nat := 7545002326691395886591

theorem tailTrace_1190201 : CollatzResearch.WordTrace tailWord_1190201 prefixEnd_1190201 7545002326691395886591 := by
  unfold tailWord_1190201
  simp only [CollatzResearch.WordTrace]
  refine ⟨43410196761112521992746457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28940131174075014661830971 43410196761112521992746457)
  ·
    refine ⟨32557647570834391494559843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43410196761112521992746457 32557647570834391494559843)
    ·
      refine ⟨48836471356251587241839765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32557647570834391494559843 48836471356251587241839765)
      ·
        refine ⟨2289209594824293151961239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48836471356251587241839765 2289209594824293151961239)
        ·
          refine ⟨3433814392236439727941859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289209594824293151961239 3433814392236439727941859)
          ·
            refine ⟨5150721588354659591912789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433814392236439727941859 5150721588354659591912789)
            ·
              refine ⟨7545002326691395886591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5150721588354659591912789 7545002326691395886591)
              ·
                rfl

theorem cell23_1190201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 11].length) (baseStart_1190201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190201 prefixEnd_1190201 := by exact prefixLift 1190201
  have htrace : WordTrace (prefixWord ++ tailWord_1190201) baseStart_1190201 baseEnd_1190201 := by
    simpa [prefixWord, tailWord_1190201, baseEnd_1190201] using wordTrace_append hprefix tailTrace_1190201
  have hstable : (prefixWord ++ tailWord_1190201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190201).length < 2 ^ (prefixWord ++ tailWord_1190201).sum := by decide
  have hdescent : baseEnd_1190201 < baseStart_1190201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190325 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 7]
def baseStart_1190325 : Nat := 118140960795 + 1190325 * 2 ^ 59
def prefixEnd_1190325 : Nat := 4983230072969 + 3 ^ 40 * 1190325 * 2
def baseEnd_1190325 : Nat := 67912095562573397962589

theorem tailTrace_1190325 : CollatzResearch.WordTrace tailWord_1190325 prefixEnd_1190325 67912095562573397962589 := by
  unfold tailWord_1190325
  simp only [CollatzResearch.WordTrace]
  refine ⟨43414719412663291170260429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28943146275108860780173619 43414719412663291170260429)
  ·
    refine ⟨16280519779748734188847661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43414719412663291170260429 16280519779748734188847661)
    ·
      refine ⟨6105194917405775320817873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16280519779748734188847661 6105194917405775320817873)
      ·
        refine ⟨4578896188054331490613405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6105194917405775320817873 4578896188054331490613405)
        ·
          refine ⟨1717086070520374308980027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4578896188054331490613405 1717086070520374308980027)
          ·
            refine ⟨2575629105780561463470041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717086070520374308980027 2575629105780561463470041)
            ·
              refine ⟨1931721829335421097602531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575629105780561463470041 1931721829335421097602531)
              ·
                refine ⟨2897582744003131646403797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931721829335421097602531 2897582744003131646403797)
                ·
                  refine ⟨67912095562573397962589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2897582744003131646403797 67912095562573397962589)
                  ·
                    rfl

theorem cell23_1190325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_1190325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190325 prefixEnd_1190325 := by exact prefixLift 1190325
  have htrace : WordTrace (prefixWord ++ tailWord_1190325) baseStart_1190325 baseEnd_1190325 := by
    simpa [prefixWord, tailWord_1190325, baseEnd_1190325] using wordTrace_append hprefix tailTrace_1190325
  have hstable : (prefixWord ++ tailWord_1190325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190325).length < 2 ^ (prefixWord ++ tailWord_1190325).sum := by decide
  have hdescent : baseEnd_1190325 < baseStart_1190325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190351 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 10]
def baseStart_1190351 : Nat := 118140960795 + 1190351 * 2 ^ 59
def prefixEnd_1190351 : Nat := 4983230072969 + 3 ^ 40 * 1190351 * 2
def baseEnd_1190351 : Nat := 203740736853392493312727

theorem tailTrace_1190351 : CollatzResearch.WordTrace tailWord_1190351 prefixEnd_1190351 203740736853392493312727 := by
  unfold tailWord_1190351
  simp only [CollatzResearch.WordTrace]
  refine ⟨43415667710569097610706907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28943778473712731740471271 43415667710569097610706907)
  ·
    refine ⟨65123501565853646416060361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43415667710569097610706907 65123501565853646416060361)
    ·
      refine ⟨48842626174390234812045271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65123501565853646416060361 48842626174390234812045271)
      ·
        refine ⟨73263939261585352218067907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48842626174390234812045271 73263939261585352218067907)
        ·
          refine ⟨109895908892378028327101861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73263939261585352218067907 109895908892378028327101861)
          ·
            refine ⟨20605482917320880311331599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109895908892378028327101861 20605482917320880311331599)
            ·
              refine ⟨30908224375981320466997399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20605482917320880311331599 30908224375981320466997399)
              ·
                refine ⟨46362336563971980700496099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30908224375981320466997399 46362336563971980700496099)
                ·
                  refine ⟨69543504845957971050744149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46362336563971980700496099 69543504845957971050744149)
                  ·
                    refine ⟨203740736853392493312727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 69543504845957971050744149 203740736853392493312727)
                    ·
                      rfl

theorem cell23_1190351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_1190351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190351 prefixEnd_1190351 := by exact prefixLift 1190351
  have htrace : WordTrace (prefixWord ++ tailWord_1190351) baseStart_1190351 baseEnd_1190351 := by
    simpa [prefixWord, tailWord_1190351, baseEnd_1190351] using wordTrace_append hprefix tailTrace_1190351
  have hstable : (prefixWord ++ tailWord_1190351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190351).length < 2 ^ (prefixWord ++ tailWord_1190351).sum := by decide
  have hdescent : baseEnd_1190351 < baseStart_1190351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190375 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1190375 : Nat := 118140960795 + 1190375 * 2 ^ 59
def prefixEnd_1190375 : Nat := 4983230072969 + 3 ^ 40 * 1190375 * 2
def baseEnd_1190375 : Nat := 611234534095885386038071

theorem tailTrace_1190375 : CollatzResearch.WordTrace tailWord_1190375 prefixEnd_1190375 611234534095885386038071 := by
  unfold tailWord_1190375
  simp only [CollatzResearch.WordTrace]
  refine ⟨43416543062482149709580579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28944362041654766473053719 43416543062482149709580579)
  ·
    refine ⟨65124814593723224564370869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43416543062482149709580579 65124814593723224564370869)
    ·
      refine ⟨6105451368161552302909769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65124814593723224564370869 6105451368161552302909769)
      ·
        refine ⟨4579088526121164227182327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6105451368161552302909769 4579088526121164227182327)
        ·
          refine ⟨6868632789181746340773491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579088526121164227182327 6868632789181746340773491)
          ·
            refine ⟨10302949183772619511160237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6868632789181746340773491 10302949183772619511160237)
            ·
              refine ⟨3863605943914732316685089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10302949183772619511160237 3863605943914732316685089)
              ·
                refine ⟨2897704457936049237513817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3863605943914732316685089 2897704457936049237513817)
                ·
                  refine ⟨2173278343452036928135363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897704457936049237513817 2173278343452036928135363)
                  ·
                    refine ⟨3259917515178055392203045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2173278343452036928135363 3259917515178055392203045)
                    ·
                      refine ⟨611234534095885386038071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3259917515178055392203045 611234534095885386038071)
                      ·
                        rfl

theorem cell23_1190375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1190375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190375 prefixEnd_1190375 := by exact prefixLift 1190375
  have htrace : WordTrace (prefixWord ++ tailWord_1190375) baseStart_1190375 baseEnd_1190375 := by
    simpa [prefixWord, tailWord_1190375, baseEnd_1190375] using wordTrace_append hprefix tailTrace_1190375
  have hstable : (prefixWord ++ tailWord_1190375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190375).length < 2 ^ (prefixWord ++ tailWord_1190375).sum := by decide
  have hdescent : baseEnd_1190375 < baseStart_1190375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190406 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1190406 : Nat := 118140960795 + 1190406 * 2 ^ 59
def prefixEnd_1190406 : Nat := 4983230072969 + 3 ^ 40 * 1190406 * 2
def baseEnd_1190406 : Nat := 203750150665391588250143

theorem tailTrace_1190406 : CollatzResearch.WordTrace tailWord_1190406 prefixEnd_1190406 203750150665391588250143 := by
  unfold tailWord_1190406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356802303917807562623721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28945115816913228002639381 1356802303917807562623721)
  ·
    refine ⟨1017601727938355671967791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1356802303917807562623721 1017601727938355671967791)
    ·
      refine ⟨1526402591907533507951687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017601727938355671967791 1526402591907533507951687)
      ·
        refine ⟨2289603887861300261927531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526402591907533507951687 2289603887861300261927531)
        ·
          refine ⟨3434405831791950392891297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289603887861300261927531 3434405831791950392891297)
          ·
            refine ⟨2575804373843962794668473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434405831791950392891297 2575804373843962794668473)
            ·
              refine ⟨1931853280382972096001355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575804373843962794668473 1931853280382972096001355)
              ·
                refine ⟨2897779920574458144002033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931853280382972096001355 2897779920574458144002033)
                ·
                  refine ⟨2173334940430843608001525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897779920574458144002033 2173334940430843608001525)
                  ·
                    refine ⟨203750150665391588250143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2173334940430843608001525 203750150665391588250143)
                    ·
                      rfl

theorem cell23_1190406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1190406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190406 prefixEnd_1190406 := by exact prefixLift 1190406
  have htrace : WordTrace (prefixWord ++ tailWord_1190406) baseStart_1190406 baseEnd_1190406 := by
    simpa [prefixWord, tailWord_1190406, baseEnd_1190406] using wordTrace_append hprefix tailTrace_1190406
  have hstable : (prefixWord ++ tailWord_1190406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190406).length < 2 ^ (prefixWord ++ tailWord_1190406).sum := by decide
  have hdescent : baseEnd_1190406 < baseStart_1190406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190412 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1190412 : Nat := 118140960795 + 1190412 * 2 ^ 59
def prefixEnd_1190412 : Nat := 4983230072969 + 3 ^ 40 * 1190412 * 2
def baseEnd_1190412 : Nat := 611253532880101741275401

theorem tailTrace_1190412 : CollatzResearch.WordTrace tailWord_1190412 prefixEnd_1190412 611253532880101741275401 := by
  unfold tailWord_1190412
  simp only [CollatzResearch.WordTrace]
  refine ⟨21708946281674052514338745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28945261708898736685784993 21708946281674052514338745)
  ·
    refine ⟨16281709711255539385754059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21708946281674052514338745 16281709711255539385754059)
    ·
      refine ⟨24422564566883309078631089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16281709711255539385754059 24422564566883309078631089)
      ·
        refine ⟨18316923425162481808973317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24422564566883309078631089 18316923425162481808973317)
        ·
          refine ⟨3434423142217965339182497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18316923425162481808973317 3434423142217965339182497)
          ·
            refine ⟨2575817356663474004386873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434423142217965339182497 2575817356663474004386873)
            ·
              refine ⟨1931863017497605503290155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575817356663474004386873 1931863017497605503290155)
              ·
                refine ⟨2897794526246408254935233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931863017497605503290155 2897794526246408254935233)
                ·
                  refine ⟨2173345894684806191201425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897794526246408254935233 2173345894684806191201425)
                  ·
                    refine ⟨1630009421013604643401069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173345894684806191201425 1630009421013604643401069)
                    ·
                      refine ⟨611253532880101741275401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630009421013604643401069 611253532880101741275401)
                      ·
                        rfl

theorem cell23_1190412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1190412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190412 prefixEnd_1190412 := by exact prefixLift 1190412
  have htrace : WordTrace (prefixWord ++ tailWord_1190412) baseStart_1190412 baseEnd_1190412 := by
    simpa [prefixWord, tailWord_1190412, baseEnd_1190412] using wordTrace_append hprefix tailTrace_1190412
  have hstable : (prefixWord ++ tailWord_1190412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190412).length < 2 ^ (prefixWord ++ tailWord_1190412).sum := by decide
  have hdescent : baseEnd_1190412 < baseStart_1190412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190425 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 3]
def baseStart_1190425 : Nat := 118140960795 + 1190425 * 2 ^ 59
def prefixEnd_1190425 : Nat := 4983230072969 + 3 ^ 40 * 1190425 * 2
def baseEnd_1190425 : Nat := 611260208128610190412841

theorem tailTrace_1190425 : CollatzResearch.WordTrace tailWord_1190425 prefixEnd_1190425 611260208128610190412841 := by
  unfold tailWord_1190425
  simp only [CollatzResearch.WordTrace]
  refine ⟨43418366712301008248900729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28945577808200672165933819 43418366712301008248900729)
  ·
    refine ⟨32563775034225756186675547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43418366712301008248900729 32563775034225756186675547)
    ·
      refine ⟨48845662551338634280013321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32563775034225756186675547 48845662551338634280013321)
      ·
        refine ⟨36634246913503975710009991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48845662551338634280013321 36634246913503975710009991)
        ·
          refine ⟨54951370370255963565014987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36634246913503975710009991 54951370370255963565014987)
          ·
            refine ⟨82427055555383945347522481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54951370370255963565014987 82427055555383945347522481)
            ·
              refine ⟨61820291666537959010641861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82427055555383945347522481 61820291666537959010641861)
              ·
                refine ⟨11591304687475867314495349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61820291666537959010641861 11591304687475867314495349)
                ·
                  refine ⟨1086684814450862560733939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11591304687475867314495349 1086684814450862560733939)
                  ·
                    refine ⟨1630027221676293841100909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1086684814450862560733939 1630027221676293841100909)
                    ·
                      refine ⟨611260208128610190412841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630027221676293841100909 611260208128610190412841)
                      ·
                        rfl

theorem cell23_1190425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_1190425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190425 prefixEnd_1190425 := by exact prefixLift 1190425
  have htrace : WordTrace (prefixWord ++ tailWord_1190425) baseStart_1190425 baseEnd_1190425 := by
    simpa [prefixWord, tailWord_1190425, baseEnd_1190425] using wordTrace_append hprefix tailTrace_1190425
  have hstable : (prefixWord ++ tailWord_1190425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190425).length < 2 ^ (prefixWord ++ tailWord_1190425).sum := by decide
  have hdescent : baseEnd_1190425 < baseStart_1190425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190432 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 6]
def baseStart_1190432 : Nat := 118140960795 + 1190432 * 2 ^ 59
def prefixEnd_1190432 : Nat := 4983230072969 + 3 ^ 40 * 1190432 * 2
def baseEnd_1190432 : Nat := 67918200277021295891701

theorem tailTrace_1190432 : CollatzResearch.WordTrace tailWord_1190432 prefixEnd_1190432 67918200277021295891701 := by
  unfold tailWord_1190432
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709311011637824222202775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28945748015517098962937033 21709311011637824222202775)
  ·
    refine ⟨32563966517456736333304163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21709311011637824222202775 32563966517456736333304163)
    ·
      refine ⟨48845949776185104499956245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32563966517456736333304163 48845949776185104499956245)
      ·
        refine ⟨2289653895758676773435449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48845949776185104499956245 2289653895758676773435449)
        ·
          refine ⟨1717240421819007580076587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2289653895758676773435449 1717240421819007580076587)
          ·
            refine ⟨2575860632728511370114881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717240421819007580076587 2575860632728511370114881)
            ·
              refine ⟨1931895474546383527586161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575860632728511370114881 1931895474546383527586161)
              ·
                refine ⟨1448921605909787645689621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1931895474546383527586161 1448921605909787645689621)
                ·
                  refine ⟨67918200277021295891701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1448921605909787645689621 67918200277021295891701)
                  ·
                    rfl

theorem cell23_1190432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_1190432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190432 prefixEnd_1190432 := by exact prefixLift 1190432
  have htrace : WordTrace (prefixWord ++ tailWord_1190432) baseStart_1190432 baseEnd_1190432 := by
    simpa [prefixWord, tailWord_1190432, baseEnd_1190432] using wordTrace_append hprefix tailTrace_1190432
  have hstable : (prefixWord ++ tailWord_1190432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190432).length < 2 ^ (prefixWord ++ tailWord_1190432).sum := by decide
  have hdescent : baseEnd_1190432 < baseStart_1190432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190436 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_1190436 : Nat := 118140960795 + 1190436 * 2 ^ 59
def prefixEnd_1190436 : Nat := 4983230072969 + 3 ^ 40 * 1190436 * 2
def baseEnd_1190436 : Nat := 203755285471936549125097

theorem tailTrace_1190436 : CollatzResearch.WordTrace tailWord_1190436 prefixEnd_1190436 203755285471936549125097 := by
  unfold tailWord_1190436
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709383957630578563775581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28945845276840771418367441 21709383957630578563775581)
  ·
    refine ⟨8141018984111466961415843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21709383957630578563775581 8141018984111466961415843)
    ·
      refine ⟨12211528476167200442123765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8141018984111466961415843 12211528476167200442123765)
      ·
        refine ⟨1144830794640675041449103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12211528476167200442123765 1144830794640675041449103)
        ·
          refine ⟨1717246191961012562173655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144830794640675041449103 1717246191961012562173655)
          ·
            refine ⟨2575869287941518843260483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717246191961012562173655 2575869287941518843260483)
            ·
              refine ⟨3863803931912278264890725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575869287941518843260483 3863803931912278264890725)
              ·
                refine ⟨724463237233552174667011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3863803931912278264890725 724463237233552174667011)
                ·
                  refine ⟨1086694855850328262000517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724463237233552174667011 1086694855850328262000517)
                  ·
                    refine ⟨203755285471936549125097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1086694855850328262000517 203755285471936549125097)
                    ·
                      rfl

theorem cell23_1190436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_1190436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190436 prefixEnd_1190436 := by exact prefixLift 1190436
  have htrace : WordTrace (prefixWord ++ tailWord_1190436) baseStart_1190436 baseEnd_1190436 := by
    simpa [prefixWord, tailWord_1190436, baseEnd_1190436] using wordTrace_append hprefix tailTrace_1190436
  have hstable : (prefixWord ++ tailWord_1190436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190436).length < 2 ^ (prefixWord ++ tailWord_1190436).sum := by decide
  have hdescent : baseEnd_1190436 < baseStart_1190436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190469 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_1190469 : Nat := 118140960795 + 1190469 * 2 ^ 59
def prefixEnd_1190469 : Nat := 4983230072969 + 3 ^ 40 * 1190469 * 2
def baseEnd_1190469 : Nat := 611282801277408018262639

theorem tailTrace_1190469 : CollatzResearch.WordTrace tailWord_1190469 prefixEnd_1190469 611282801277408018262639 := by
  unfold tailWord_1190469
  simp only [CollatzResearch.WordTrace]
  refine ⟨43419971524141603763502461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28946647682761069175668307 43419971524141603763502461)
  ·
    refine ⟨16282489321553101411313423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43419971524141603763502461 16282489321553101411313423)
    ·
      refine ⟨24423733982329652116970135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16282489321553101411313423 24423733982329652116970135)
      ·
        refine ⟨36635600973494478175455203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24423733982329652116970135 36635600973494478175455203)
        ·
          refine ⟨54953401460241717263182805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36635600973494478175455203 54953401460241717263182805)
          ·
            refine ⟨1287970346724415248355847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54953401460241717263182805 1287970346724415248355847)
            ·
              refine ⟨1931955520086622872533771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287970346724415248355847 1931955520086622872533771)
              ·
                refine ⟨2897933280129934308800657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931955520086622872533771 2897933280129934308800657)
                ·
                  refine ⟨2173449960097450731600493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897933280129934308800657 2173449960097450731600493)
                  ·
                    refine ⟨815043735036544024350185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173449960097450731600493 815043735036544024350185)
                    ·
                      refine ⟨611282801277408018262639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815043735036544024350185 611282801277408018262639)
                      ·
                        rfl

theorem cell23_1190469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_1190469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190469 prefixEnd_1190469 := by exact prefixLift 1190469
  have htrace : WordTrace (prefixWord ++ tailWord_1190469) baseStart_1190469 baseEnd_1190469 := by
    simpa [prefixWord, tailWord_1190469, baseEnd_1190469] using wordTrace_append hprefix tailTrace_1190469
  have hstable : (prefixWord ++ tailWord_1190469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190469).length < 2 ^ (prefixWord ++ tailWord_1190469).sum := by decide
  have hdescent : baseEnd_1190469 < baseStart_1190469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190482 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1190482 : Nat := 118140960795 + 1190482 * 2 ^ 59
def prefixEnd_1190482 : Nat := 4983230072969 + 3 ^ 40 * 1190482 * 2
def baseEnd_1190482 : Nat := 611289476525916467400079

theorem tailTrace_1190482 : CollatzResearch.WordTrace tailWord_1190482 prefixEnd_1190482 611289476525916467400079 := by
  unfold tailWord_1190482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10855111418273626745931425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28946963782063004655817133 10855111418273626745931425)
  ·
    refine ⟨8141333563705220059448569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10855111418273626745931425 8141333563705220059448569)
    ·
      refine ⟨6106000172778915044586427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8141333563705220059448569 6106000172778915044586427)
      ·
        refine ⟨9159000259168372566879641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6106000172778915044586427 9159000259168372566879641)
        ·
          refine ⟨6869250194376279425159731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9159000259168372566879641 6869250194376279425159731)
          ·
            refine ⟨10303875291564419137739597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6869250194376279425159731 10303875291564419137739597)
            ·
              refine ⟨3863953234336657176652349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10303875291564419137739597 3863953234336657176652349)
              ·
                refine ⟨1448982462876246441244631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3863953234336657176652349 1448982462876246441244631)
                ·
                  refine ⟨2173473694314369661866947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448982462876246441244631 2173473694314369661866947)
                  ·
                    refine ⟨3260210541471554492800421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2173473694314369661866947 3260210541471554492800421)
                    ·
                      refine ⟨611289476525916467400079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3260210541471554492800421 611289476525916467400079)
                      ·
                        rfl

theorem cell23_1190482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1190482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190482 prefixEnd_1190482 := by exact prefixLift 1190482
  have htrace : WordTrace (prefixWord ++ tailWord_1190482) baseStart_1190482 baseEnd_1190482 := by
    simpa [prefixWord, tailWord_1190482, baseEnd_1190482] using wordTrace_append hprefix tailTrace_1190482
  have hstable : (prefixWord ++ tailWord_1190482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190482).length < 2 ^ (prefixWord ++ tailWord_1190482).sum := by decide
  have hdescent : baseEnd_1190482 < baseStart_1190482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190499 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 3, 2, 2]
def baseStart_1190499 : Nat := 118140960795 + 1190499 * 2 ^ 59
def prefixEnd_1190499 : Nat := 4983230072969 + 3 ^ 40 * 1190499 * 2
def baseEnd_1190499 : Nat := 611298205697042900887501

theorem tailTrace_1190499 : CollatzResearch.WordTrace tailWord_1190499 prefixEnd_1190499 611298205697042900887501 := by
  unfold tailWord_1190499
  simp only [CollatzResearch.WordTrace]
  refine ⟨43421065714032918887094551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28947377142688612591396367 43421065714032918887094551)
  ·
    refine ⟨65131598571049378330641827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43421065714032918887094551 65131598571049378330641827)
    ·
      refine ⟨97697397856574067495962741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65131598571049378330641827 97697397856574067495962741)
      ·
        refine ⟨9159131049053818827746507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97697397856574067495962741 9159131049053818827746507)
        ·
          refine ⟨13738696573580728241619761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9159131049053818827746507 13738696573580728241619761)
          ·
            refine ⟨10304022430185546181214821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13738696573580728241619761 10304022430185546181214821)
            ·
              refine ⟨1932004205659789908977779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10304022430185546181214821 1932004205659789908977779)
              ·
                refine ⟨2898006308489684863466669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932004205659789908977779 2898006308489684863466669)
                ·
                  refine ⟨1086752365683631823800001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2898006308489684863466669 1086752365683631823800001)
                  ·
                    refine ⟨815064274262723867850001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086752365683631823800001 815064274262723867850001)
                    ·
                      refine ⟨611298205697042900887501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815064274262723867850001 611298205697042900887501)
                      ·
                        rfl

theorem cell23_1190499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_1190499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190499 prefixEnd_1190499 := by exact prefixLift 1190499
  have htrace : WordTrace (prefixWord ++ tailWord_1190499) baseStart_1190499 baseEnd_1190499 := by
    simpa [prefixWord, tailWord_1190499, baseEnd_1190499] using wordTrace_append hprefix tailTrace_1190499
  have hstable : (prefixWord ++ tailWord_1190499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190499).length < 2 ^ (prefixWord ++ tailWord_1190499).sum := by decide
  have hdescent : baseEnd_1190499 < baseStart_1190499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190515 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3]
def baseStart_1190515 : Nat := 118140960795 + 1190515 * 2 ^ 59
def prefixEnd_1190515 : Nat := 4983230072969 + 3 ^ 40 * 1190515 * 2
def baseEnd_1190515 : Nat := 611306421387514838287427

theorem tailTrace_1190515 : CollatzResearch.WordTrace tailWord_1190515 prefixEnd_1190515 611306421387514838287427 := by
  unfold tailWord_1190515
  simp only [CollatzResearch.WordTrace]
  refine ⟨43421649281974953619676999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28947766187983302413117999 43421649281974953619676999)
  ·
    refine ⟨65132473922962430429515499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43421649281974953619676999 65132473922962430429515499)
    ·
      refine ⟨97698710884443645644273249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65132473922962430429515499 97698710884443645644273249)
      ·
        refine ⟨73274033163332734233204937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97698710884443645644273249 73274033163332734233204937)
        ·
          refine ⟨54955524872499550674903703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73274033163332734233204937 54955524872499550674903703)
          ·
            refine ⟨82433287308749326012355555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54955524872499550674903703 82433287308749326012355555)
            ·
              refine ⟨123649930963123989018533333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82433287308749326012355555 123649930963123989018533333)
              ·
                refine ⟨2898045256948218492621875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123649930963123989018533333 2898045256948218492621875)
                ·
                  refine ⟨4347067885422327738932813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898045256948218492621875 4347067885422327738932813)
                  ·
                    refine ⟨1630150457033372902099805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4347067885422327738932813 1630150457033372902099805)
                    ·
                      refine ⟨611306421387514838287427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630150457033372902099805 611306421387514838287427)
                      ·
                        rfl

theorem cell23_1190515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_1190515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190515 prefixEnd_1190515 := by exact prefixLift 1190515
  have htrace : WordTrace (prefixWord ++ tailWord_1190515) baseStart_1190515 baseEnd_1190515 := by
    simpa [prefixWord, tailWord_1190515, baseEnd_1190515] using wordTrace_append hprefix tailTrace_1190515
  have hstable : (prefixWord ++ tailWord_1190515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190515).length < 2 ^ (prefixWord ++ tailWord_1190515).sum := by decide
  have hdescent : baseEnd_1190515 < baseStart_1190515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190533 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 1, 2, 2]
def baseStart_1190533 : Nat := 118140960795 + 1190533 * 2 ^ 59
def prefixEnd_1190533 : Nat := 4983230072969 + 3 ^ 40 * 1190533 * 2
def baseEnd_1190533 : Nat := 611315664039295767862345

theorem tailTrace_1190533 : CollatzResearch.WordTrace tailWord_1190533 prefixEnd_1190533 611315664039295767862345 := by
  unfold tailWord_1190533
  simp only [CollatzResearch.WordTrace]
  refine ⟨43422305795909742693832253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28948203863939828462554835 43422305795909742693832253)
  ·
    refine ⟨16283364673466153510187095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43422305795909742693832253 16283364673466153510187095)
    ·
      refine ⟨24425047010199230265280643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16283364673466153510187095 24425047010199230265280643)
      ·
        refine ⟨36637570515298845397920965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24425047010199230265280643 36637570515298845397920965)
        ·
          refine ⟨6869544471618533512110181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36637570515298845397920965 6869544471618533512110181)
          ·
            refine ⟨1288039588428475033520659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6869544471618533512110181 1288039588428475033520659)
            ·
              refine ⟨1932059382642712550280989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288039588428475033520659 1932059382642712550280989)
              ·
                refine ⟨724522268491017206355371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932059382642712550280989 724522268491017206355371)
                ·
                  refine ⟨1086783402736525809533057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724522268491017206355371 1086783402736525809533057)
                  ·
                    refine ⟨815087552052394357149793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086783402736525809533057 815087552052394357149793)
                    ·
                      refine ⟨611315664039295767862345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815087552052394357149793 611315664039295767862345)
                      ·
                        rfl

theorem cell23_1190533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_1190533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190533 prefixEnd_1190533 := by exact prefixLift 1190533
  have htrace : WordTrace (prefixWord ++ tailWord_1190533) baseStart_1190533 baseEnd_1190533 := by
    simpa [prefixWord, tailWord_1190533, baseEnd_1190533] using wordTrace_append hprefix tailTrace_1190533
  have hstable : (prefixWord ++ tailWord_1190533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190533).length < 2 ^ (prefixWord ++ tailWord_1190533).sum := by decide
  have hdescent : baseEnd_1190533 < baseStart_1190533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190570 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1190570 : Nat := 118140960795 + 1190570 * 2 ^ 59
def prefixEnd_1190570 : Nat := 4983230072969 + 3 ^ 40 * 1190570 * 2
def baseEnd_1190570 : Nat := 611334662823512123099675

theorem tailTrace_1190570 : CollatzResearch.WordTrace tailWord_1190570 prefixEnd_1190570 611334662823512123099675 := by
  unfold tailWord_1190570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10855913824193924503232291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28949103531183798675286109 10855913824193924503232291)
  ·
    refine ⟨16283870736290886754848437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10855913824193924503232291 16283870736290886754848437)
    ·
      refine ⟨1526612881527270633267041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16283870736290886754848437 1526612881527270633267041)
      ·
        refine ⟨1144959661145452974950281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1526612881527270633267041 1144959661145452974950281)
        ·
          refine ⟨858719745859089731212711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1144959661145452974950281 858719745859089731212711)
          ·
            refine ⟨1288079618788634596819067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858719745859089731212711 1288079618788634596819067)
            ·
              refine ⟨1932119428182951895228601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288079618788634596819067 1932119428182951895228601)
              ·
                refine ⟨1449089571137213921421451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932119428182951895228601 1449089571137213921421451)
                ·
                  refine ⟨2173634356705820882132177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449089571137213921421451 2173634356705820882132177)
                  ·
                    refine ⟨1630225767529365661599133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2173634356705820882132177 1630225767529365661599133)
                    ·
                      refine ⟨611334662823512123099675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630225767529365661599133 611334662823512123099675)
                      ·
                        rfl

theorem cell23_1190570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1190570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190570 prefixEnd_1190570 := by exact prefixLift 1190570
  have htrace : WordTrace (prefixWord ++ tailWord_1190570) baseStart_1190570 baseEnd_1190570 := by
    simpa [prefixWord, tailWord_1190570, baseEnd_1190570] using wordTrace_append hprefix tailTrace_1190570
  have hstable : (prefixWord ++ tailWord_1190570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190570).length < 2 ^ (prefixWord ++ tailWord_1190570).sum := by decide
  have hdescent : baseEnd_1190570 < baseStart_1190570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190575 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_1190575 : Nat := 118140960795 + 1190575 * 2 ^ 59
def prefixEnd_1190575 : Nat := 4983230072969 + 3 ^ 40 * 1190575 * 2
def baseEnd_1190575 : Nat := 611337230226784603537151

theorem tailTrace_1190575 : CollatzResearch.WordTrace tailWord_1190575 prefixEnd_1190575 611337230226784603537151 := by
  unfold tailWord_1190575
  simp only [CollatzResearch.WordTrace]
  refine ⟨43423837661757583866861179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28949225107838389244574119 43423837661757583866861179)
  ·
    refine ⟨65135756492636375800291769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43423837661757583866861179 65135756492636375800291769)
    ·
      refine ⟨48851817369477281850218827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65135756492636375800291769 48851817369477281850218827)
      ·
        refine ⟨73277726054215922775328241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48851817369477281850218827 73277726054215922775328241)
        ·
          refine ⟨54958294540661942081496181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73277726054215922775328241 54958294540661942081496181)
          ·
            refine ⟨5152340113187057070140267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54958294540661942081496181 5152340113187057070140267)
            ·
              refine ⟨7728510169780585605210401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152340113187057070140267 7728510169780585605210401)
              ·
                refine ⟨5796382627335439203907801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7728510169780585605210401 5796382627335439203907801)
                ·
                  refine ⟨4347286970501579402930851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5796382627335439203907801 4347286970501579402930851)
                  ·
                    refine ⟨6520930455752369104396277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4347286970501579402930851 6520930455752369104396277)
                    ·
                      refine ⟨611337230226784603537151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6520930455752369104396277 611337230226784603537151)
                      ·
                        rfl

theorem cell23_1190575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_1190575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190575 prefixEnd_1190575 := by exact prefixLift 1190575
  have htrace : WordTrace (prefixWord ++ tailWord_1190575) baseStart_1190575 baseEnd_1190575 := by
    simpa [prefixWord, tailWord_1190575, baseEnd_1190575] using wordTrace_append hprefix tailTrace_1190575
  have hstable : (prefixWord ++ tailWord_1190575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190575).length < 2 ^ (prefixWord ++ tailWord_1190575).sum := by decide
  have hdescent : baseEnd_1190575 < baseStart_1190575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190585 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1190585 : Nat := 118140960795 + 1190585 * 2 ^ 59
def prefixEnd_1190585 : Nat := 4983230072969 + 3 ^ 40 * 1190585 * 2
def baseEnd_1190585 : Nat := 611342365033329564412105

theorem tailTrace_1190585 : CollatzResearch.WordTrace tailWord_1190585 prefixEnd_1190585 611342365033329564412105 := by
  unfold tailWord_1190585
  simp only [CollatzResearch.WordTrace]
  refine ⟨43424202391721355574725209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28949468261147570383150139 43424202391721355574725209)
  ·
    refine ⟨32568151793791016681043907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43424202391721355574725209 32568151793791016681043907)
    ·
      refine ⟨48852227690686525021565861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32568151793791016681043907 48852227690686525021565861)
      ·
        refine ⟨9159792692003723441543599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48852227690686525021565861 9159792692003723441543599)
        ·
          refine ⟨13739689038005585162315399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9159792692003723441543599 13739689038005585162315399)
          ·
            refine ⟨20609533557008377743473099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13739689038005585162315399 20609533557008377743473099)
            ·
              refine ⟨30914300335512566615209649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20609533557008377743473099 30914300335512566615209649)
              ·
                refine ⟨23185725251634424961407237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30914300335512566615209649 23185725251634424961407237)
                ·
                  refine ⟨4347323484681454680263857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23185725251634424961407237 4347323484681454680263857)
                  ·
                    refine ⟨3260492613511091010197893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4347323484681454680263857 3260492613511091010197893)
                    ·
                      refine ⟨611342365033329564412105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3260492613511091010197893 611342365033329564412105)
                      ·
                        rfl

theorem cell23_1190585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1190585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190585 prefixEnd_1190585 := by exact prefixLift 1190585
  have htrace : WordTrace (prefixWord ++ tailWord_1190585) baseStart_1190585 baseEnd_1190585 := by
    simpa [prefixWord, tailWord_1190585, baseEnd_1190585] using wordTrace_append hprefix tailTrace_1190585
  have hstable : (prefixWord ++ tailWord_1190585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190585).length < 2 ^ (prefixWord ++ tailWord_1190585).sum := by decide
  have hdescent : baseEnd_1190585 < baseStart_1190585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190589 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_1190589 : Nat := 118140960795 + 1190589 * 2 ^ 59
def prefixEnd_1190589 : Nat := 4983230072969 + 3 ^ 40 * 1190589 * 2
def baseEnd_1190589 : Nat := 611344418955947548762087

theorem tailTrace_1190589 : CollatzResearch.WordTrace tailWord_1190589 prefixEnd_1190589 611344418955947548762087 := by
  unfold tailWord_1190589
  simp only [CollatzResearch.WordTrace]
  refine ⟨43424348283706864257870821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28949565522471242838580547 43424348283706864257870821)
  ·
    refine ⟨8142065303195037048350779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43424348283706864257870821 8142065303195037048350779)
    ·
      refine ⟨12213097954792555572526169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142065303195037048350779 12213097954792555572526169)
      ·
        refine ⟨9159823466094416679394627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12213097954792555572526169 9159823466094416679394627)
        ·
          refine ⟨13739735199141625019091941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9159823466094416679394627 13739735199141625019091941)
          ·
            refine ⟨2576200349839054691079739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13739735199141625019091941 2576200349839054691079739)
            ·
              refine ⟨3864300524758582036619609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576200349839054691079739 3864300524758582036619609)
              ·
                refine ⟨2898225393568936527464707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3864300524758582036619609 2898225393568936527464707)
                ·
                  refine ⟨4347338090353404791197061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898225393568936527464707 4347338090353404791197061)
                  ·
                    refine ⟨815125891941263398349449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347338090353404791197061 815125891941263398349449)
                    ·
                      refine ⟨611344418955947548762087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815125891941263398349449 611344418955947548762087)
                      ·
                        rfl

theorem cell23_1190589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_1190589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190589 prefixEnd_1190589 := by exact prefixLift 1190589
  have htrace : WordTrace (prefixWord ++ tailWord_1190589) baseStart_1190589 baseEnd_1190589 := by
    simpa [prefixWord, tailWord_1190589, baseEnd_1190589] using wordTrace_append hprefix tailTrace_1190589
  have hstable : (prefixWord ++ tailWord_1190589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190589).length < 2 ^ (prefixWord ++ tailWord_1190589).sum := by decide
  have hdescent : baseEnd_1190589 < baseStart_1190589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190606 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_1190606 : Nat := 118140960795 + 1190606 * 2 ^ 59
def prefixEnd_1190606 : Nat := 4983230072969 + 3 ^ 40 * 1190606 * 2
def baseEnd_1190606 : Nat := 611353148127073982249509

theorem tailTrace_1190606 : CollatzResearch.WordTrace tailWord_1190606 prefixEnd_1190606 611353148127073982249509 := by
  unfold tailWord_1190606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5428121040580659520154959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28949978883096850774159781 5428121040580659520154959)
  ·
    refine ⟨8142181560870989280232439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5428121040580659520154959 8142181560870989280232439)
    ·
      refine ⟨12213272341306483920348659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142181560870989280232439 12213272341306483920348659)
      ·
        refine ⟨18319908511959725880522989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12213272341306483920348659 18319908511959725880522989)
        ·
          refine ⟨6869965691984897205196121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18319908511959725880522989 6869965691984897205196121)
          ·
            refine ⟨5152474268988672903897091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6869965691984897205196121 5152474268988672903897091)
            ·
              refine ⟨7728711403483009355845637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5152474268988672903897091 7728711403483009355845637)
              ·
                refine ⟨1449133388153064254221057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7728711403483009355845637 1449133388153064254221057)
                ·
                  refine ⟨1086850041114798190665793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449133388153064254221057 1086850041114798190665793)
                  ·
                    refine ⟨815137530836098642999345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086850041114798190665793 815137530836098642999345)
                    ·
                      refine ⟨611353148127073982249509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815137530836098642999345 611353148127073982249509)
                      ·
                        rfl

theorem cell23_1190606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_1190606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190606 prefixEnd_1190606 := by exact prefixLift 1190606
  have htrace : WordTrace (prefixWord ++ tailWord_1190606) baseStart_1190606 baseEnd_1190606 := by
    simpa [prefixWord, tailWord_1190606, baseEnd_1190606] using wordTrace_append hprefix tailTrace_1190606
  have hstable : (prefixWord ++ tailWord_1190606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190606).length < 2 ^ (prefixWord ++ tailWord_1190606).sum := by decide
  have hdescent : baseEnd_1190606 < baseStart_1190606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190642 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_1190642 : Nat := 118140960795 + 1190642 * 2 ^ 59
def prefixEnd_1190642 : Nat := 4983230072969 + 3 ^ 40 * 1190642 * 2
def baseEnd_1190642 : Nat := 203790544476878613799781

theorem tailTrace_1190642 : CollatzResearch.WordTrace tailWord_1190642 prefixEnd_1190642 203790544476878613799781 := by
  unfold tailWord_1190642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856570338128713577387545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28950854235009902873033453 10856570338128713577387545)
  ·
    refine ⟨8142427753596535183040659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10856570338128713577387545 8142427753596535183040659)
    ·
      refine ⟨12213641630394802774560989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142427753596535183040659 12213641630394802774560989)
      ·
        refine ⟨4580115611398051040460371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12213641630394802774560989 4580115611398051040460371)
        ·
          refine ⟨6870173417097076560690557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4580115611398051040460371 6870173417097076560690557)
          ·
            refine ⟨2576315031411403710258959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6870173417097076560690557 2576315031411403710258959)
            ·
              refine ⟨3864472547117105565388439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576315031411403710258959 3864472547117105565388439)
              ·
                refine ⟨5796708820675658348082659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864472547117105565388439 5796708820675658348082659)
                ·
                  refine ⟨8695063231013487522123989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5796708820675658348082659 8695063231013487522123989)
                  ·
                    refine ⟨203790544476878613799781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8695063231013487522123989 203790544476878613799781)
                    ·
                      rfl

theorem cell23_1190642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_1190642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190642 prefixEnd_1190642 := by exact prefixLift 1190642
  have htrace : WordTrace (prefixWord ++ tailWord_1190642) baseStart_1190642 baseEnd_1190642 := by
    simpa [prefixWord, tailWord_1190642, baseEnd_1190642] using wordTrace_append hprefix tailTrace_1190642
  have hstable : (prefixWord ++ tailWord_1190642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190642).length < 2 ^ (prefixWord ++ tailWord_1190642).sum := by decide
  have hdescent : baseEnd_1190642 < baseStart_1190642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190644 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1190644 : Nat := 118140960795 + 1190644 * 2 ^ 59
def prefixEnd_1190644 : Nat := 4983230072969 + 3 ^ 40 * 1190644 * 2
def baseEnd_1190644 : Nat := 611372660391944833574335

theorem tailTrace_1190644 : CollatzResearch.WordTrace tailWord_1190644 prefixEnd_1190644 611372660391944833574335 := by
  unfold tailWord_1190644
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713177149253804325561493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28950902865671739100748657 21713177149253804325561493)
  ·
    refine ⟨1017805178871272077760695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21713177149253804325561493 1017805178871272077760695)
    ·
      refine ⟨1526707768306908116641043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017805178871272077760695 1526707768306908116641043)
      ·
        refine ⟨2290061652460362174961565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526707768306908116641043 2290061652460362174961565)
        ·
          refine ⟨858773119672635815610587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2290061652460362174961565 858773119672635815610587)
          ·
            refine ⟨1288159679508953723415881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858773119672635815610587 1288159679508953723415881)
            ·
              refine ⟨966119759631715292561911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288159679508953723415881 966119759631715292561911)
              ·
                refine ⟨1449179639447572938842867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966119759631715292561911 1449179639447572938842867)
                ·
                  refine ⟨2173769459171359408264301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449179639447572938842867 2173769459171359408264301)
                  ·
                    refine ⟨815163547189259778099113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173769459171359408264301 815163547189259778099113)
                    ·
                      refine ⟨611372660391944833574335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815163547189259778099113 611372660391944833574335)
                      ·
                        rfl

theorem cell23_1190644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1190644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190644 prefixEnd_1190644 := by exact prefixLift 1190644
  have htrace : WordTrace (prefixWord ++ tailWord_1190644) baseStart_1190644 baseEnd_1190644 := by
    simpa [prefixWord, tailWord_1190644, baseEnd_1190644] using wordTrace_append hprefix tailTrace_1190644
  have hstable : (prefixWord ++ tailWord_1190644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190644).length < 2 ^ (prefixWord ++ tailWord_1190644).sum := by decide
  have hdescent : baseEnd_1190644 < baseStart_1190644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190665 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_1190665 : Nat := 118140960795 + 1190665 * 2 ^ 59
def prefixEnd_1190665 : Nat := 4983230072969 + 3 ^ 40 * 1190665 * 2
def baseEnd_1190665 : Nat := 611383443485689251411737

theorem tailTrace_1190665 : CollatzResearch.WordTrace tailWord_1190665 prefixEnd_1190665 611383443485689251411737 := by
  unfold tailWord_1190665
  simp only [CollatzResearch.WordTrace]
  refine ⟨43427120231431529237637449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28951413487621019491758299 43427120231431529237637449)
  ·
    refine ⟨32570340173573646928228087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43427120231431529237637449 32570340173573646928228087)
    ·
      refine ⟨48855510260360470392342131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32570340173573646928228087 48855510260360470392342131)
      ·
        refine ⟨73283265390540705588513197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48855510260360470392342131 73283265390540705588513197)
        ·
          refine ⟨27481224521452764595692449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73283265390540705588513197 27481224521452764595692449)
          ·
            refine ⟨20610918391089573446769337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27481224521452764595692449 20610918391089573446769337)
            ·
              refine ⟨15458188793317180085077003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20610918391089573446769337 15458188793317180085077003)
              ·
                refine ⟨23187283189975770127615505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15458188793317180085077003 23187283189975770127615505)
                ·
                  refine ⟨17390462392481827595711629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23187283189975770127615505 17390462392481827595711629)
                  ·
                    refine ⟨6521423397180685348391861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17390462392481827595711629 6521423397180685348391861)
                    ·
                      refine ⟨611383443485689251411737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6521423397180685348391861 611383443485689251411737)
                      ·
                        rfl

theorem cell23_1190665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_1190665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190665 prefixEnd_1190665 := by exact prefixLift 1190665
  have htrace : WordTrace (prefixWord ++ tailWord_1190665) baseStart_1190665 baseEnd_1190665 := by
    simpa [prefixWord, tailWord_1190665, baseEnd_1190665] using wordTrace_append hprefix tailTrace_1190665
  have hstable : (prefixWord ++ tailWord_1190665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190665).length < 2 ^ (prefixWord ++ tailWord_1190665).sum := by decide
  have hdescent : baseEnd_1190665 < baseStart_1190665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190675 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_1190675 : Nat := 118140960795 + 1190675 * 2 ^ 59
def prefixEnd_1190675 : Nat := 4983230072969 + 3 ^ 40 * 1190675 * 2
def baseEnd_1190675 : Nat := 611388578292234212286691

theorem tailTrace_1190675 : CollatzResearch.WordTrace tailWord_1190675 prefixEnd_1190675 611388578292234212286691 := by
  unfold tailWord_1190675
  simp only [CollatzResearch.WordTrace]
  refine ⟨43427484961395300945501479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28951656640930200630334319 43427484961395300945501479)
  ·
    refine ⟨65141227442092951418252219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43427484961395300945501479 65141227442092951418252219)
    ·
      refine ⟨97711841163139427127378329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65141227442092951418252219 97711841163139427127378329)
      ·
        refine ⟨73283880872354570345533747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97711841163139427127378329 73283880872354570345533747)
        ·
          refine ⟨109925821308531855518300621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73283880872354570345533747 109925821308531855518300621)
          ·
            refine ⟨41222182990699445819362733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109925821308531855518300621 41222182990699445819362733)
            ·
              refine ⟨15458318621512292182261025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41222182990699445819362733 15458318621512292182261025)
              ·
                refine ⟨11593738966134219136695769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15458318621512292182261025 11593738966134219136695769)
                ·
                  refine ⟨8695304224600664352521827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11593738966134219136695769 8695304224600664352521827)
                  ·
                    refine ⟨13042956336900996528782741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8695304224600664352521827 13042956336900996528782741)
                    ·
                      refine ⟨611388578292234212286691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13042956336900996528782741 611388578292234212286691)
                      ·
                        rfl

theorem cell23_1190675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_1190675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190675 prefixEnd_1190675 := by exact prefixLift 1190675
  have htrace : WordTrace (prefixWord ++ tailWord_1190675) baseStart_1190675 baseEnd_1190675 := by
    simpa [prefixWord, tailWord_1190675, baseEnd_1190675] using wordTrace_append hprefix tailTrace_1190675
  have hstable : (prefixWord ++ tailWord_1190675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190675).length < 2 ^ (prefixWord ++ tailWord_1190675).sum := by decide
  have hdescent : baseEnd_1190675 < baseStart_1190675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190682 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1190682 : Nat := 118140960795 + 1190682 * 2 ^ 59
def prefixEnd_1190682 : Nat := 4983230072969 + 3 ^ 40 * 1190682 * 2
def baseEnd_1190682 : Nat := 611392172656815684899159

theorem tailTrace_1190682 : CollatzResearch.WordTrace tailWord_1190682 prefixEnd_1190682 611392172656815684899159 := by
  unfold tailWord_1190682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856935068092485285251575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28951826848246627427337533 10856935068092485285251575)
  ·
    refine ⟨16285402602138727927877363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856935068092485285251575 16285402602138727927877363)
    ·
      refine ⟨24428103903208091891816045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16285402602138727927877363 24428103903208091891816045)
      ·
        refine ⟨9160538963703034459431017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24428103903208091891816045 9160538963703034459431017)
        ·
          refine ⟨6870404222777275844573263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160538963703034459431017 6870404222777275844573263)
          ·
            refine ⟨10305606334165913766859895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6870404222777275844573263 10305606334165913766859895)
            ·
              refine ⟨15458409501248870650289843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10305606334165913766859895 15458409501248870650289843)
              ·
                refine ⟨23187614251873305975434765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15458409501248870650289843 23187614251873305975434765)
                ·
                  refine ⟨8695355344452489740788037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23187614251873305975434765 8695355344452489740788037)
                  ·
                    refine ⟨1630379127084841826397757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8695355344452489740788037 1630379127084841826397757)
                    ·
                      refine ⟨611392172656815684899159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630379127084841826397757 611392172656815684899159)
                      ·
                        rfl

theorem cell23_1190682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1190682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190682 prefixEnd_1190682 := by exact prefixLift 1190682
  have htrace : WordTrace (prefixWord ++ tailWord_1190682) baseStart_1190682 baseEnd_1190682 := by
    simpa [prefixWord, tailWord_1190682, baseEnd_1190682] using wordTrace_append hprefix tailTrace_1190682
  have hstable : (prefixWord ++ tailWord_1190682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190682).length < 2 ^ (prefixWord ++ tailWord_1190682).sum := by decide
  have hdescent : baseEnd_1190682 < baseStart_1190682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190735 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_1190735 : Nat := 118140960795 + 1190735 * 2 ^ 59
def prefixEnd_1190735 : Nat := 4983230072969 + 3 ^ 40 * 1190735 * 2
def baseEnd_1190735 : Nat := 611419387131503977536415

theorem tailTrace_1190735 : CollatzResearch.WordTrace tailWord_1190735 prefixEnd_1190735 611419387131503977536415 := by
  unfold tailWord_1190735
  simp only [CollatzResearch.WordTrace]
  refine ⟨43429673341177931192685659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28953115560785287461790439 43429673341177931192685659)
  ·
    refine ⟨65144510011766896789028489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43429673341177931192685659 65144510011766896789028489)
    ·
      refine ⟨48858382508825172591771367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65144510011766896789028489 48858382508825172591771367)
      ·
        refine ⟨73287573763237758887657051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48858382508825172591771367 73287573763237758887657051)
        ·
          refine ⟨109931360644856638331485577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73287573763237758887657051 109931360644856638331485577)
          ·
            refine ⟨82448520483642478748614183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109931360644856638331485577 82448520483642478748614183)
            ·
              refine ⟨123672780725463718122921275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82448520483642478748614183 123672780725463718122921275)
              ·
                refine ⟨185509171088195577184381913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123672780725463718122921275 185509171088195577184381913)
                ·
                  refine ⟨139131878316146682888286435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185509171088195577184381913 139131878316146682888286435)
                  ·
                    refine ⟨208697817474220024332429653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139131878316146682888286435 208697817474220024332429653)
                    ·
                      refine ⟨611419387131503977536415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 208697817474220024332429653 611419387131503977536415)
                      ·
                        rfl

theorem cell23_1190735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_1190735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190735 prefixEnd_1190735 := by exact prefixLift 1190735
  have htrace : WordTrace (prefixWord ++ tailWord_1190735) baseStart_1190735 baseEnd_1190735 := by
    simpa [prefixWord, tailWord_1190735, baseEnd_1190735] using wordTrace_append hprefix tailTrace_1190735
  have hstable : (prefixWord ++ tailWord_1190735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190735).length < 2 ^ (prefixWord ++ tailWord_1190735).sum := by decide
  have hdescent : baseEnd_1190735 < baseStart_1190735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190756 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_1190756 : Nat := 118140960795 + 1190756 * 2 ^ 59
def prefixEnd_1190756 : Nat := 4983230072969 + 3 ^ 40 * 1190756 * 2
def baseEnd_1190756 : Nat := 611430170225248395373819

theorem tailTrace_1190756 : CollatzResearch.WordTrace tailWord_1190756 prefixEnd_1190756 611430170225248395373819 := by
  unfold tailWord_1190756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21715219637050925889600061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28953626182734567852800081 21715219637050925889600061)
  ·
    refine ⟨8143207363894097208600023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21715219637050925889600061 8143207363894097208600023)
    ·
      refine ⟨12214811045841145812900035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8143207363894097208600023 12214811045841145812900035)
      ·
        refine ⟨18322216568761718719350053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12214811045841145812900035 18322216568761718719350053)
        ·
          refine ⟨3435415606642822259878135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18322216568761718719350053 3435415606642822259878135)
          ·
            refine ⟨5153123409964233389817203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435415606642822259878135 5153123409964233389817203)
            ·
              refine ⟨7729685114946350084725805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153123409964233389817203 7729685114946350084725805)
              ·
                refine ⟨2898631918104881281772177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7729685114946350084725805 2898631918104881281772177)
                ·
                  refine ⟨2173973938578660961329133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2898631918104881281772177 2173973938578660961329133)
                  ·
                    refine ⟨815240226966997860498425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173973938578660961329133 815240226966997860498425)
                    ·
                      refine ⟨611430170225248395373819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815240226966997860498425 611430170225248395373819)
                      ·
                        rfl

theorem cell23_1190756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_1190756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190756 prefixEnd_1190756 := by exact prefixLift 1190756
  have htrace : WordTrace (prefixWord ++ tailWord_1190756) baseStart_1190756 baseEnd_1190756 := by
    simpa [prefixWord, tailWord_1190756, baseEnd_1190756] using wordTrace_append hprefix tailTrace_1190756
  have hstable : (prefixWord ++ tailWord_1190756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190756).length < 2 ^ (prefixWord ++ tailWord_1190756).sum := by decide
  have hdescent : baseEnd_1190756 < baseStart_1190756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190779 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 2, 4]
def baseStart_1190779 : Nat := 118140960795 + 1190779 * 2 ^ 59
def prefixEnd_1190779 : Nat := 4983230072969 + 3 ^ 40 * 1190779 * 2
def baseEnd_1190779 : Nat := 203813993426767268462071

theorem tailTrace_1190779 : CollatzResearch.WordTrace tailWord_1190779 prefixEnd_1190779 203813993426767268462071 := by
  unfold tailWord_1190779
  simp only [CollatzResearch.WordTrace]
  refine ⟨43431278153018526707287391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28954185435345684471524927 43431278153018526707287391)
  ·
    refine ⟨65146917229527790060931087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43431278153018526707287391 65146917229527790060931087)
    ·
      refine ⟨97720375844291685091396631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65146917229527790060931087 97720375844291685091396631)
      ·
        refine ⟨146580563766437527637094947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97720375844291685091396631 146580563766437527637094947)
        ·
          refine ⟨219870845649656291455642421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146580563766437527637094947 219870845649656291455642421)
          ·
            refine ⟨20612891779655277323966477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 219870845649656291455642421 20612891779655277323966477)
            ·
              refine ⟨7729834417370728996487429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20612891779655277323966477 7729834417370728996487429)
              ·
                refine ⟨1449343953257011686841393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7729834417370728996487429 1449343953257011686841393)
                ·
                  refine ⟨1087007964942758765131045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449343953257011686841393 1087007964942758765131045)
                  ·
                    refine ⟨203813993426767268462071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087007964942758765131045 203813993426767268462071)
                    ·
                      rfl

theorem cell23_1190779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 4].length) (baseStart_1190779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190779 prefixEnd_1190779 := by exact prefixLift 1190779
  have htrace : WordTrace (prefixWord ++ tailWord_1190779) baseStart_1190779 baseEnd_1190779 := by
    simpa [prefixWord, tailWord_1190779, baseEnd_1190779] using wordTrace_append hprefix tailTrace_1190779
  have hstable : (prefixWord ++ tailWord_1190779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190779).length < 2 ^ (prefixWord ++ tailWord_1190779).sum := by decide
  have hdescent : baseEnd_1190779 < baseStart_1190779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190789 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_1190789 : Nat := 118140960795 + 1190789 * 2 ^ 59
def prefixEnd_1190789 : Nat := 4983230072969 + 3 ^ 40 * 1190789 * 2
def baseEnd_1190789 : Nat := 611447115086846766261167

theorem tailTrace_1190789 : CollatzResearch.WordTrace tailWord_1190789 prefixEnd_1190789 611447115086846766261167 := by
  unfold tailWord_1190789
  simp only [CollatzResearch.WordTrace]
  refine ⟨43431642882982298415151421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28954428588654865610100947 43431642882982298415151421)
  ·
    refine ⟨16286866081118361905681783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43431642882982298415151421 16286866081118361905681783)
    ·
      refine ⟨24430299121677542858522675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16286866081118361905681783 24430299121677542858522675)
      ·
        refine ⟨36645448682516314287784013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24430299121677542858522675 36645448682516314287784013)
        ·
          refine ⟨13742043255943617857919005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36645448682516314287784013 13742043255943617857919005)
          ·
            refine ⟨5153266220978856696719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13742043255943617857919005 5153266220978856696719627)
            ·
              refine ⟨7729899331468285045079441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5153266220978856696719627 7729899331468285045079441)
              ·
                refine ⟨5797424498601213783809581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7729899331468285045079441 5797424498601213783809581)
                ·
                  refine ⟨2174034186975455168928593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5797424498601213783809581 2174034186975455168928593)
                  ·
                    refine ⟨1630525640231591376696445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2174034186975455168928593 1630525640231591376696445)
                    ·
                      refine ⟨611447115086846766261167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630525640231591376696445 611447115086846766261167)
                      ·
                        rfl

theorem cell23_1190789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_1190789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190789 prefixEnd_1190789 := by exact prefixLift 1190789
  have htrace : WordTrace (prefixWord ++ tailWord_1190789) baseStart_1190789 baseEnd_1190789 := by
    simpa [prefixWord, tailWord_1190789, baseEnd_1190789] using wordTrace_append hprefix tailTrace_1190789
  have hstable : (prefixWord ++ tailWord_1190789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190789).length < 2 ^ (prefixWord ++ tailWord_1190789).sum := by decide
  have hdescent : baseEnd_1190789 < baseStart_1190789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190819 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1190819 : Nat := 118140960795 + 1190819 * 2 ^ 59
def prefixEnd_1190819 : Nat := 4983230072969 + 3 ^ 40 * 1190819 * 2
def baseEnd_1190819 : Nat := 611462519506481648886029

theorem tailTrace_1190819 : CollatzResearch.WordTrace tailWord_1190819 prefixEnd_1190819 611462519506481648886029 := by
  unfold tailWord_1190819
  simp only [CollatzResearch.WordTrace]
  refine ⟨43432737072873613538743511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28955158048582409025829007 43432737072873613538743511)
  ·
    refine ⟨65149105609310420308115267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43432737072873613538743511 65149105609310420308115267)
    ·
      refine ⟨97723658413965630462172901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65149105609310420308115267 97723658413965630462172901)
      ·
        refine ⟨18323185952618555711657419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97723658413965630462172901 18323185952618555711657419)
        ·
          refine ⟨27484778928927833567486129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18323185952618555711657419 27484778928927833567486129)
          ·
            refine ⟨20613584196695875175614597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27484778928927833567486129 20613584196695875175614597)
            ·
              refine ⟨3865047036880476595427737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20613584196695875175614597 3865047036880476595427737)
              ·
                refine ⟨2898785277660357446570803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865047036880476595427737 2898785277660357446570803)
                ·
                  refine ⟨4348177916490536169856205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898785277660357446570803 4348177916490536169856205)
                  ·
                    refine ⟨1630566718683951063696077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4348177916490536169856205 1630566718683951063696077)
                    ·
                      refine ⟨611462519506481648886029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630566718683951063696077 611462519506481648886029)
                      ·
                        rfl

theorem cell23_1190819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1190819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190819 prefixEnd_1190819 := by exact prefixLift 1190819
  have htrace : WordTrace (prefixWord ++ tailWord_1190819) baseStart_1190819 baseEnd_1190819 := by
    simpa [prefixWord, tailWord_1190819, baseEnd_1190819] using wordTrace_append hprefix tailTrace_1190819
  have hstable : (prefixWord ++ tailWord_1190819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190819).length < 2 ^ (prefixWord ++ tailWord_1190819).sum := by decide
  have hdescent : baseEnd_1190819 < baseStart_1190819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190820 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_1190820 : Nat := 118140960795 + 1190820 * 2 ^ 59
def prefixEnd_1190820 : Nat := 4983230072969 + 3 ^ 40 * 1190820 * 2
def baseEnd_1190820 : Nat := 611463032987136144973525

theorem tailTrace_1190820 : CollatzResearch.WordTrace tailWord_1190820 prefixEnd_1190820 611463032987136144973525 := by
  unfold tailWord_1190820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716386772934995354764957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28955182363913327139686609 21716386772934995354764957)
  ·
    refine ⟨8143645039850623258036859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21716386772934995354764957 8143645039850623258036859)
    ·
      refine ⟨12215467559775934887055289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8143645039850623258036859 12215467559775934887055289)
      ·
        refine ⟨9161600669831951165291467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12215467559775934887055289 9161600669831951165291467)
        ·
          refine ⟨13742401004747926747937201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9161600669831951165291467 13742401004747926747937201)
          ·
            refine ⟨10306800753560945060952901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13742401004747926747937201 10306800753560945060952901)
            ·
              refine ⟨1932525141292677198928669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10306800753560945060952901 1932525141292677198928669)
              ·
                refine ⟨724696927984753949598251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932525141292677198928669 724696927984753949598251)
                ·
                  refine ⟨1087045391977130924397377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724696927984753949598251 1087045391977130924397377)
                  ·
                    refine ⟨815284043982848193298033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1087045391977130924397377 815284043982848193298033)
                    ·
                      refine ⟨611463032987136144973525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815284043982848193298033 611463032987136144973525)
                      ·
                        rfl

theorem cell23_1190820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_1190820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190820 prefixEnd_1190820 := by exact prefixLift 1190820
  have htrace : WordTrace (prefixWord ++ tailWord_1190820) baseStart_1190820 baseEnd_1190820 := by
    simpa [prefixWord, tailWord_1190820, baseEnd_1190820] using wordTrace_append hprefix tailTrace_1190820
  have hstable : (prefixWord ++ tailWord_1190820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190820).length < 2 ^ (prefixWord ++ tailWord_1190820).sum := by decide
  have hdescent : baseEnd_1190820 < baseStart_1190820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190823 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1190823 : Nat := 118140960795 + 1190823 * 2 ^ 59
def prefixEnd_1190823 : Nat := 4983230072969 + 3 ^ 40 * 1190823 * 2
def baseEnd_1190823 : Nat := 611464573429099633236011

theorem tailTrace_1190823 : CollatzResearch.WordTrace tailWord_1190823 prefixEnd_1190823 611464573429099633236011 := by
  unfold tailWord_1190823
  simp only [CollatzResearch.WordTrace]
  refine ⟨43432882964859122221889123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28955255309906081481259415 43432882964859122221889123)
  ·
    refine ⟨65149324447288683332833685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43432882964859122221889123 65149324447288683332833685)
    ·
      refine ⟨3053874583466657031226579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65149324447288683332833685 3053874583466657031226579)
      ·
        refine ⟨4580811875199985546839869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053874583466657031226579 4580811875199985546839869)
        ·
          refine ⟨1717804453199994580064951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4580811875199985546839869 1717804453199994580064951)
          ·
            refine ⟨2576706679799991870097427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717804453199994580064951 2576706679799991870097427)
            ·
              refine ⟨3865060019699987805146141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576706679799991870097427 3865060019699987805146141)
              ·
                refine ⟨1449397507387495426929803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865060019699987805146141 1449397507387495426929803)
                ·
                  refine ⟨2174096261081243140394705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449397507387495426929803 2174096261081243140394705)
                  ·
                    refine ⟨1630572195810932355296029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2174096261081243140394705 1630572195810932355296029)
                    ·
                      refine ⟨611464573429099633236011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630572195810932355296029 611464573429099633236011)
                      ·
                        rfl

theorem cell23_1190823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1190823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190823 prefixEnd_1190823 := by exact prefixLift 1190823
  have htrace : WordTrace (prefixWord ++ tailWord_1190823) baseStart_1190823 baseEnd_1190823 := by
    simpa [prefixWord, tailWord_1190823, baseEnd_1190823] using wordTrace_append hprefix tailTrace_1190823
  have hstable : (prefixWord ++ tailWord_1190823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190823).length < 2 ^ (prefixWord ++ tailWord_1190823).sum := by decide
  have hdescent : baseEnd_1190823 < baseStart_1190823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190854 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1190854 : Nat := 118140960795 + 1190854 * 2 ^ 59
def prefixEnd_1190854 : Nat := 4983230072969 + 3 ^ 40 * 1190854 * 2
def baseEnd_1190854 : Nat := 611480491329389011948369

theorem tailTrace_1190854 : CollatzResearch.WordTrace tailWord_1190854 prefixEnd_1190854 611480491329389011948369 := by
  unfold tailWord_1190854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357312925867087953633363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28956009085164543010845077 1357312925867087953633363)
  ·
    refine ⟨2035969388800631930450045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357312925867087953633363 2035969388800631930450045)
    ·
      refine ⟨763488520800236973918767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2035969388800631930450045 763488520800236973918767)
      ·
        refine ⟨1145232781200355460878151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763488520800236973918767 1145232781200355460878151)
        ·
          refine ⟨1717849171800533191317227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145232781200355460878151 1717849171800533191317227)
          ·
            refine ⟨2576773757700799786975841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717849171800533191317227 2576773757700799786975841)
            ·
              refine ⟨1932580318275599840231881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576773757700799786975841 1932580318275599840231881)
              ·
                refine ⟨1449435238706699880173911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932580318275599840231881 1449435238706699880173911)
                ·
                  refine ⟨2174152858060049820260867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449435238706699880173911 2174152858060049820260867)
                  ·
                    refine ⟨3261229287090074730391301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174152858060049820260867 3261229287090074730391301)
                    ·
                      refine ⟨611480491329389011948369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3261229287090074730391301 611480491329389011948369)
                      ·
                        rfl

theorem cell23_1190854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1190854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190854 prefixEnd_1190854 := by exact prefixLift 1190854
  have htrace : WordTrace (prefixWord ++ tailWord_1190854) baseStart_1190854 baseEnd_1190854 := by
    simpa [prefixWord, tailWord_1190854, baseEnd_1190854] using wordTrace_append hprefix tailTrace_1190854
  have hstable : (prefixWord ++ tailWord_1190854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190854).length < 2 ^ (prefixWord ++ tailWord_1190854).sum := by decide
  have hdescent : baseEnd_1190854 < baseStart_1190854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190863 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 1, 3, 2]
def baseStart_1190863 : Nat := 118140960795 + 1190863 * 2 ^ 59
def prefixEnd_1190863 : Nat := 4983230072969 + 3 ^ 40 * 1190863 * 2
def baseEnd_1190863 : Nat := 611485112655279476735827

theorem tailTrace_1190863 : CollatzResearch.WordTrace tailWord_1190863 prefixEnd_1190863 611485112655279476735827 := by
  unfold tailWord_1190863
  simp only [CollatzResearch.WordTrace]
  refine ⟨43434341884714209053345243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28956227923142806035563495 43434341884714209053345243)
  ·
    refine ⟨65151512827071313580017865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43434341884714209053345243 65151512827071313580017865)
    ·
      refine ⟨48863634620303485185013399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65151512827071313580017865 48863634620303485185013399)
      ·
        refine ⟨73295451930455227777520099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48863634620303485185013399 73295451930455227777520099)
        ·
          refine ⟨109943177895682841666280149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73295451930455227777520099 109943177895682841666280149)
          ·
            refine ⟨2576793231930066601553441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109943177895682841666280149 2576793231930066601553441)
            ·
              refine ⟨1932594923947549951165081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576793231930066601553441 1932594923947549951165081)
              ·
                refine ⟨1449446192960662463373811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932594923947549951165081 1449446192960662463373811)
                ·
                  refine ⟨2174169289440993695060717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449446192960662463373811 2174169289440993695060717)
                  ·
                    refine ⟨815313483540372635647769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174169289440993695060717 815313483540372635647769)
                    ·
                      refine ⟨611485112655279476735827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815313483540372635647769 611485112655279476735827)
                      ·
                        rfl

theorem cell23_1190863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3, 2].length) (baseStart_1190863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190863 prefixEnd_1190863 := by exact prefixLift 1190863
  have htrace : WordTrace (prefixWord ++ tailWord_1190863) baseStart_1190863 baseEnd_1190863 := by
    simpa [prefixWord, tailWord_1190863, baseEnd_1190863] using wordTrace_append hprefix tailTrace_1190863
  have hstable : (prefixWord ++ tailWord_1190863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190863).length < 2 ^ (prefixWord ++ tailWord_1190863).sum := by decide
  have hdescent : baseEnd_1190863 < baseStart_1190863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190909 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1190909 : Nat := 118140960795 + 1190909 * 2 ^ 59
def prefixEnd_1190909 : Nat := 4983230072969 + 3 ^ 40 * 1190909 * 2
def baseEnd_1190909 : Nat := 611508732765386296760615

theorem tailTrace_1190909 : CollatzResearch.WordTrace tailWord_1190909 prefixEnd_1190909 611508732765386296760615 := by
  unfold tailWord_1190909
  simp only [CollatzResearch.WordTrace]
  refine ⟨43436019642547558909519781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28957346428365039273013187 43436019642547558909519781)
  ·
    refine ⟨8144253682977667295534959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43436019642547558909519781 8144253682977667295534959)
    ·
      refine ⟨12216380524466500943302439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144253682977667295534959 12216380524466500943302439)
      ·
        refine ⟨18324570786699751414953659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12216380524466500943302439 18324570786699751414953659)
        ·
          refine ⟨27486856180049627122430489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18324570786699751414953659 27486856180049627122430489)
          ·
            refine ⟨20615142135037220341822867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27486856180049627122430489 20615142135037220341822867)
            ·
              refine ⟨30922713202555830512734301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20615142135037220341822867 30922713202555830512734301)
              ·
                refine ⟨11596017450958436442275363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30922713202555830512734301 11596017450958436442275363)
                ·
                  refine ⟨17394026176437654663413045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11596017450958436442275363 17394026176437654663413045)
                  ·
                    refine ⟨1630689954041030124694973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17394026176437654663413045 1630689954041030124694973)
                    ·
                      refine ⟨611508732765386296760615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1630689954041030124694973 611508732765386296760615)
                      ·
                        rfl

theorem cell23_1190909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1190909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190909 prefixEnd_1190909 := by exact prefixLift 1190909
  have htrace : WordTrace (prefixWord ++ tailWord_1190909) baseStart_1190909 baseEnd_1190909 := by
    simpa [prefixWord, tailWord_1190909, baseEnd_1190909] using wordTrace_append hprefix tailTrace_1190909
  have hstable : (prefixWord ++ tailWord_1190909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190909).length < 2 ^ (prefixWord ++ tailWord_1190909).sum := by decide
  have hdescent : baseEnd_1190909 < baseStart_1190909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190914 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1190914 : Nat := 118140960795 + 1190914 * 2 ^ 59
def prefixEnd_1190914 : Nat := 4983230072969 + 3 ^ 40 * 1190914 * 2
def baseEnd_1190914 : Nat := 611511300168658777198093

theorem tailTrace_1190914 : CollatzResearch.WordTrace tailWord_1190914 prefixEnd_1190914 611511300168658777198093 := by
  unfold tailWord_1190914
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859050501882361190862949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28957468005019629842301197 10859050501882361190862949)
  ·
    refine ⟨2036071969102942723286803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10859050501882361190862949 2036071969102942723286803)
    ·
      refine ⟨3054107953654414084930205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036071969102942723286803 3054107953654414084930205)
      ·
        refine ⟨1145290482620405281848827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3054107953654414084930205 1145290482620405281848827)
        ·
          refine ⟨1717935723930607922773241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145290482620405281848827 1717935723930607922773241)
          ·
            refine ⟨1288451792947955942079931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717935723930607922773241 1288451792947955942079931)
            ·
              refine ⟨1932677689421933913119897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288451792947955942079931 1932677689421933913119897)
              ·
                refine ⟨1449508267066450434839923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932677689421933913119897 1449508267066450434839923)
                ·
                  refine ⟨2174262400599675652259885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449508267066450434839923 2174262400599675652259885)
                  ·
                    refine ⟨815348400224878369597457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174262400599675652259885 815348400224878369597457)
                    ·
                      refine ⟨611511300168658777198093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815348400224878369597457 611511300168658777198093)
                      ·
                        rfl

theorem cell23_1190914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1190914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190914 prefixEnd_1190914 := by exact prefixLift 1190914
  have htrace : WordTrace (prefixWord ++ tailWord_1190914) baseStart_1190914 baseEnd_1190914 := by
    simpa [prefixWord, tailWord_1190914, baseEnd_1190914] using wordTrace_append hprefix tailTrace_1190914
  have hstable : (prefixWord ++ tailWord_1190914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190914).length < 2 ^ (prefixWord ++ tailWord_1190914).sum := by decide
  have hdescent : baseEnd_1190914 < baseStart_1190914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190946 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1190946 : Nat := 118140960795 + 1190946 * 2 ^ 59
def prefixEnd_1190946 : Nat := 4983230072969 + 3 ^ 40 * 1190946 * 2
def baseEnd_1190946 : Nat := 203842577183200883999315

theorem tailTrace_1190946 : CollatzResearch.WordTrace tailWord_1190946 prefixEnd_1190946 203842577183200883999315 := by
  unfold tailWord_1190946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859342285853378557154173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28958246095609009485744461 10859342285853378557154173)
  ·
    refine ⟨4072253357195016958932815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10859342285853378557154173 4072253357195016958932815)
    ·
      refine ⟨6108380035792525438399223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4072253357195016958932815 6108380035792525438399223)
      ·
        refine ⟨9162570053688788157598835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6108380035792525438399223 9162570053688788157598835)
        ·
          refine ⟨13743855080533182236398253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9162570053688788157598835 13743855080533182236398253)
          ·
            refine ⟨5153945655199943338649345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13743855080533182236398253 5153945655199943338649345)
            ·
              refine ⟨3865459241399957503987009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153945655199943338649345 3865459241399957503987009)
              ·
                refine ⟨2899094431049968127990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865459241399957503987009 2899094431049968127990257)
                ·
                  refine ⟨2174320823287476095992693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899094431049968127990257 2174320823287476095992693)
                  ·
                    refine ⟨203842577183200883999315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2174320823287476095992693 203842577183200883999315)
                    ·
                      rfl

theorem cell23_1190946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1190946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190946 prefixEnd_1190946 := by exact prefixLift 1190946
  have htrace : WordTrace (prefixWord ++ tailWord_1190946) baseStart_1190946 baseEnd_1190946 := by
    simpa [prefixWord, tailWord_1190946, baseEnd_1190946] using wordTrace_append hprefix tailTrace_1190946
  have hstable : (prefixWord ++ tailWord_1190946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190946).length < 2 ^ (prefixWord ++ tailWord_1190946).sum := by decide
  have hdescent : baseEnd_1190946 < baseStart_1190946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190976 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_1190976 : Nat := 118140960795 + 1190976 * 2 ^ 59
def prefixEnd_1190976 : Nat := 4983230072969 + 3 ^ 40 * 1190976 * 2
def baseEnd_1190976 : Nat := 203847711989745844874269

theorem tailTrace_1190976 : CollatzResearch.WordTrace tailWord_1190976 prefixEnd_1190976 203847711989745844874269 := by
  unfold tailWord_1190976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21719231666652414676104391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28958975555536552901472521 21719231666652414676104391)
  ·
    refine ⟨32578847499978622014156587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21719231666652414676104391 32578847499978622014156587)
    ·
      refine ⟨48868271249967933021234881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32578847499978622014156587 48868271249967933021234881)
      ·
        refine ⟨36651203437475949765926161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48868271249967933021234881 36651203437475949765926161)
        ·
          refine ⟨27488402578106962324444621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36651203437475949765926161 27488402578106962324444621)
          ·
            refine ⟨10308150966790110871666733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27488402578106962324444621 10308150966790110871666733)
            ·
              refine ⟨3865556612546291576875025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10308150966790110871666733 3865556612546291576875025)
              ·
                refine ⟨2899167459409718682656269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865556612546291576875025 2899167459409718682656269)
                ·
                  refine ⟨1087187797278644505996101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2899167459409718682656269 1087187797278644505996101)
                  ·
                    refine ⟨203847711989745844874269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087187797278644505996101 203847711989745844874269)
                    ·
                      rfl

theorem cell23_1190976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_1190976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190976 prefixEnd_1190976 := by exact prefixLift 1190976
  have htrace : WordTrace (prefixWord ++ tailWord_1190976) baseStart_1190976 baseEnd_1190976 := by
    simpa [prefixWord, tailWord_1190976, baseEnd_1190976] using wordTrace_append hprefix tailTrace_1190976
  have hstable : (prefixWord ++ tailWord_1190976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190976).length < 2 ^ (prefixWord ++ tailWord_1190976).sum := by decide
  have hdescent : baseEnd_1190976 < baseStart_1190976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190983 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_1190983 : Nat := 118140960795 + 1190983 * 2 ^ 59
def prefixEnd_1190983 : Nat := 4983230072969 + 3 ^ 40 * 1190983 * 2
def baseEnd_1190983 : Nat := 611546730333819007235275

theorem tailTrace_1190983 : CollatzResearch.WordTrace tailWord_1190983 prefixEnd_1190983 611546730333819007235275 := by
  unfold tailWord_1190983
  simp only [CollatzResearch.WordTrace]
  refine ⟨43438718644279469547713603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28959145762852979698475735 43438718644279469547713603)
  ·
    refine ⟨65158077966419204321570405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43438718644279469547713603 65158077966419204321570405)
    ·
      refine ⟨12217139618703600810294451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65158077966419204321570405 12217139618703600810294451)
      ·
        refine ⟨18325709428055401215441677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12217139618703600810294451 18325709428055401215441677)
        ·
          refine ⟨6872141035520775455790629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18325709428055401215441677 6872141035520775455790629)
          ·
            refine ⟨1288526444160145397960743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6872141035520775455790629 1288526444160145397960743)
            ·
              refine ⟨1932789666240218096941115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288526444160145397960743 1932789666240218096941115)
              ·
                refine ⟨2899184499360327145411673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932789666240218096941115 2899184499360327145411673)
                ·
                  refine ⟨2174388374520245359058755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899184499360327145411673 2174388374520245359058755)
                  ·
                    refine ⟨3261582561780368038588133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174388374520245359058755 3261582561780368038588133)
                    ·
                      refine ⟨611546730333819007235275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3261582561780368038588133 611546730333819007235275)
                      ·
                        rfl

theorem cell23_1190983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_1190983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190983 prefixEnd_1190983 := by exact prefixLift 1190983
  have htrace : WordTrace (prefixWord ++ tailWord_1190983) baseStart_1190983 baseEnd_1190983 := by
    simpa [prefixWord, tailWord_1190983, baseEnd_1190983] using wordTrace_append hprefix tailTrace_1190983
  have hstable : (prefixWord ++ tailWord_1190983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190983).length < 2 ^ (prefixWord ++ tailWord_1190983).sum := by decide
  have hdescent : baseEnd_1190983 < baseStart_1190983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190993 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 1, 4]
def baseStart_1190993 : Nat := 118140960795 + 1190993 * 2 ^ 59
def prefixEnd_1190993 : Nat := 4983230072969 + 3 ^ 40 * 1190993 * 2
def baseEnd_1190993 : Nat := 203850621713454656036743

theorem tailTrace_1190993 : CollatzResearch.WordTrace tailWord_1190993 prefixEnd_1190993 203850621713454656036743 := by
  unfold tailWord_1190993
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439083374243241255577633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28959388916162160837051755 43439083374243241255577633)
  ·
    refine ⟨32579312530682430941683225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43439083374243241255577633 32579312530682430941683225)
    ·
      refine ⟨24434484398011823206262419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32579312530682430941683225 24434484398011823206262419)
      ·
        refine ⟨36651726597017734809393629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24434484398011823206262419 36651726597017734809393629)
        ·
          refine ⟨13744397473881650553522611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36651726597017734809393629 13744397473881650553522611)
          ·
            refine ⟨20616596210822475830283917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13744397473881650553522611 20616596210822475830283917)
            ·
              refine ⟨7731223579058428436356469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20616596210822475830283917 7731223579058428436356469)
              ·
                refine ⟨724802210536727665908419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7731223579058428436356469 724802210536727665908419)
                ·
                  refine ⟨1087203315805091498862629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724802210536727665908419 1087203315805091498862629)
                  ·
                    refine ⟨203850621713454656036743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087203315805091498862629 203850621713454656036743)
                    ·
                      rfl

theorem cell23_1190993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_1190993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1190993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1190993 prefixEnd_1190993 := by exact prefixLift 1190993
  have htrace : WordTrace (prefixWord ++ tailWord_1190993) baseStart_1190993 baseEnd_1190993 := by
    simpa [prefixWord, tailWord_1190993, baseEnd_1190993] using wordTrace_append hprefix tailTrace_1190993
  have hstable : (prefixWord ++ tailWord_1190993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190993).length < 2 ^ (prefixWord ++ tailWord_1190993).sum := by decide
  have hdescent : baseEnd_1190993 < baseStart_1190993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191009 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1191009 : Nat := 118140960795 + 1191009 * 2 ^ 59
def prefixEnd_1191009 : Nat := 4983230072969 + 3 ^ 40 * 1191009 * 2
def baseEnd_1191009 : Nat := 611560080830835905510155

theorem tailTrace_1191009 : CollatzResearch.WordTrace tailWord_1191009 prefixEnd_1191009 611560080830835905510155 := by
  unfold tailWord_1191009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439666942185275988160081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28959777961456850658773387 43439666942185275988160081)
  ·
    refine ⟨32579750206638956991120061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43439666942185275988160081 32579750206638956991120061)
    ·
      refine ⟨12217406327489608871670023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32579750206638956991120061 12217406327489608871670023)
      ·
        refine ⟨18326109491234413307505035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12217406327489608871670023 18326109491234413307505035)
        ·
          refine ⟨27489164236851619961257553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18326109491234413307505035 27489164236851619961257553)
          ·
            refine ⟨20616873177638714970943165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27489164236851619961257553 20616873177638714970943165)
            ·
              refine ⟨7731327441614518114103687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20616873177638714970943165 7731327441614518114103687)
              ·
                refine ⟨11596991162421777171155531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731327441614518114103687 11596991162421777171155531)
                ·
                  refine ⟨17395486743632665756733297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11596991162421777171155531 17395486743632665756733297)
                  ·
                    refine ⟨13046615057724499317549973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17395486743632665756733297 13046615057724499317549973)
                    ·
                      refine ⟨611560080830835905510155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13046615057724499317549973 611560080830835905510155)
                      ·
                        rfl

theorem cell23_1191009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1191009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191009 prefixEnd_1191009 := by exact prefixLift 1191009
  have htrace : WordTrace (prefixWord ++ tailWord_1191009) baseStart_1191009 baseEnd_1191009 := by
    simpa [prefixWord, tailWord_1191009, baseEnd_1191009] using wordTrace_append hprefix tailTrace_1191009
  have hstable : (prefixWord ++ tailWord_1191009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191009).length < 2 ^ (prefixWord ++ tailWord_1191009).sum := by decide
  have hdescent : baseEnd_1191009 < baseStart_1191009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191010 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1191010 : Nat := 118140960795 + 1191010 * 2 ^ 59
def prefixEnd_1191010 : Nat := 4983230072969 + 3 ^ 40 * 1191010 * 2
def baseEnd_1191010 : Nat := 203853531437163467199217

theorem tailTrace_1191010 : CollatzResearch.WordTrace tailWord_1191010 prefixEnd_1191010 203853531437163467199217 := by
  unfold tailWord_1191010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859925853795413289736621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28959802276787768772630989 10859925853795413289736621)
  ·
    refine ⟨4072472195173279983651233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10859925853795413289736621 4072472195173279983651233)
    ·
      refine ⟨3054354146379959987738425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4072472195173279983651233 3054354146379959987738425)
      ·
        refine ⟨2290765609784969990803819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3054354146379959987738425 2290765609784969990803819)
        ·
          refine ⟨3436148414677454986205729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290765609784969990803819 3436148414677454986205729)
          ·
            refine ⟨2577111311008091239654297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436148414677454986205729 2577111311008091239654297)
            ·
              refine ⟨1932833483256068429740723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577111311008091239654297 1932833483256068429740723)
              ·
                refine ⟨2899250224884102644611085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932833483256068429740723 2899250224884102644611085)
                ·
                  refine ⟨1087218834331538491729157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2899250224884102644611085 1087218834331538491729157)
                  ·
                    refine ⟨203853531437163467199217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087218834331538491729157 203853531437163467199217)
                    ·
                      rfl

theorem cell23_1191010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1191010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191010 prefixEnd_1191010 := by exact prefixLift 1191010
  have htrace : WordTrace (prefixWord ++ tailWord_1191010) baseStart_1191010 baseEnd_1191010 := by
    simpa [prefixWord, tailWord_1191010, baseEnd_1191010] using wordTrace_append hprefix tailTrace_1191010
  have hstable : (prefixWord ++ tailWord_1191010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191010).length < 2 ^ (prefixWord ++ tailWord_1191010).sum := by decide
  have hdescent : baseEnd_1191010 < baseStart_1191010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191039 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1191039 : Nat := 118140960795 + 1191039 * 2 ^ 59
def prefixEnd_1191039 : Nat := 4983230072969 + 3 ^ 40 * 1191039 * 2
def baseEnd_1191039 : Nat := 611575485250470788135017

theorem tailTrace_1191039 : CollatzResearch.WordTrace tailWord_1191039 prefixEnd_1191039 611575485250470788135017 := by
  unfold tailWord_1191039
  simp only [CollatzResearch.WordTrace]
  refine ⟨43440761132076591111752171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28960507421384394074501447 43440761132076591111752171)
  ·
    refine ⟨65161141698114886667628257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43440761132076591111752171 65161141698114886667628257)
    ·
      refine ⟨48870856273586165000721193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65161141698114886667628257 48870856273586165000721193)
      ·
        refine ⟨36653142205189623750540895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48870856273586165000721193 36653142205189623750540895)
        ·
          refine ⟨54979713307784435625811343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36653142205189623750540895 54979713307784435625811343)
          ·
            refine ⟨82469569961676653438717015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54979713307784435625811343 82469569961676653438717015)
            ·
              refine ⟨123704354942514980158075523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82469569961676653438717015 123704354942514980158075523)
              ·
                refine ⟨185556532413772470237113285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123704354942514980158075523 185556532413772470237113285)
                ·
                  refine ⟨34791849827582338169458741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185556532413772470237113285 34791849827582338169458741)
                  ·
                    refine ⟨3261735921335844203386757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34791849827582338169458741 3261735921335844203386757)
                    ·
                      refine ⟨611575485250470788135017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3261735921335844203386757 611575485250470788135017)
                      ·
                        rfl

theorem cell23_1191039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1191039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191039 prefixEnd_1191039 := by exact prefixLift 1191039
  have htrace : WordTrace (prefixWord ++ tailWord_1191039) baseStart_1191039 baseEnd_1191039 := by
    simpa [prefixWord, tailWord_1191039, baseEnd_1191039] using wordTrace_append hprefix tailTrace_1191039
  have hstable : (prefixWord ++ tailWord_1191039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191039).length < 2 ^ (prefixWord ++ tailWord_1191039).sum := by decide
  have hdescent : baseEnd_1191039 < baseStart_1191039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191043 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 2, 3, 2]
def baseStart_1191043 : Nat := 118140960795 + 1191043 * 2 ^ 59
def prefixEnd_1191043 : Nat := 4983230072969 + 3 ^ 40 * 1191043 * 2
def baseEnd_1191043 : Nat := 611577539173088772484999

theorem tailTrace_1191043 : CollatzResearch.WordTrace tailWord_1191043 prefixEnd_1191043 611577539173088772484999 := by
  unfold tailWord_1191043
  simp only [CollatzResearch.WordTrace]
  refine ⟨43440907024062099794897783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28960604682708066529931855 43440907024062099794897783)
  ·
    refine ⟨65161360536093149692346675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43440907024062099794897783 65161360536093149692346675)
    ·
      refine ⟨97742040804139724538520013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65161360536093149692346675 97742040804139724538520013)
      ·
        refine ⟨36653265301552396701945005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97742040804139724538520013 36653265301552396701945005)
        ·
          refine ⟨13744974488082148763229377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36653265301552396701945005 13744974488082148763229377)
          ·
            refine ⟨10308730866061611572422033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13744974488082148763229377 10308730866061611572422033)
            ·
              refine ⟨7731548149546208679316525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10308730866061611572422033 7731548149546208679316525)
              ·
                refine ⟨2899330556079828254743697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7731548149546208679316525 2899330556079828254743697)
                ·
                  refine ⟨2174497917059871191057773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899330556079828254743697 2174497917059871191057773)
                  ·
                    refine ⟨815436718897451696646665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174497917059871191057773 815436718897451696646665)
                    ·
                      refine ⟨611577539173088772484999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815436718897451696646665 611577539173088772484999)
                      ·
                        rfl

theorem cell23_1191043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_1191043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191043 prefixEnd_1191043 := by exact prefixLift 1191043
  have htrace : WordTrace (prefixWord ++ tailWord_1191043) baseStart_1191043 baseEnd_1191043 := by
    simpa [prefixWord, tailWord_1191043, baseEnd_1191043] using wordTrace_append hprefix tailTrace_1191043
  have hstable : (prefixWord ++ tailWord_1191043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191043).length < 2 ^ (prefixWord ++ tailWord_1191043).sum := by decide
  have hdescent : baseEnd_1191043 < baseStart_1191043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191090 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1191090 : Nat := 118140960795 + 1191090 * 2 ^ 59
def prefixEnd_1191090 : Nat := 4983230072969 + 3 ^ 40 * 1191090 * 2
def baseEnd_1191090 : Nat := 611601672763850088597283

theorem tailTrace_1191090 : CollatzResearch.WordTrace tailWord_1191090 prefixEnd_1191090 611601672763850088597283 := by
  unfold tailWord_1191090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860655313722956705464681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28961747503261217881239149 10860655313722956705464681)
  ·
    refine ⟨8145491485292217529098511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10860655313722956705464681 8145491485292217529098511)
    ·
      refine ⟨12218237227938326293647767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8145491485292217529098511 12218237227938326293647767)
      ·
        refine ⟨18327355841907489440471651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12218237227938326293647767 18327355841907489440471651)
        ·
          refine ⟨27491033762861234160707477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18327355841907489440471651 27491033762861234160707477)
          ·
            refine ⟨1288642207634120351283163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27491033762861234160707477 1288642207634120351283163)
            ·
              refine ⟨1932963311451180526924745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288642207634120351283163 1932963311451180526924745)
              ·
                refine ⟨1449722483588385395193559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932963311451180526924745 1449722483588385395193559)
                ·
                  refine ⟨2174583725382578092790339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449722483588385395193559 2174583725382578092790339)
                  ·
                    refine ⟨3261875588073867139185509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174583725382578092790339 3261875588073867139185509)
                    ·
                      refine ⟨611601672763850088597283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3261875588073867139185509 611601672763850088597283)
                      ·
                        rfl

theorem cell23_1191090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1191090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191090 prefixEnd_1191090 := by exact prefixLift 1191090
  have htrace : WordTrace (prefixWord ++ tailWord_1191090) baseStart_1191090 baseEnd_1191090 := by
    simpa [prefixWord, tailWord_1191090, baseEnd_1191090] using wordTrace_append hprefix tailTrace_1191090
  have hstable : (prefixWord ++ tailWord_1191090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191090).length < 2 ^ (prefixWord ++ tailWord_1191090).sum := by decide
  have hdescent : baseEnd_1191090 < baseStart_1191090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191140 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_1191140 : Nat := 118140960795 + 1191140 * 2 ^ 59
def prefixEnd_1191140 : Nat := 4983230072969 + 3 ^ 40 * 1191140 * 2
def baseEnd_1191140 : Nat := 611627346796574892972053

theorem tailTrace_1191140 : CollatzResearch.WordTrace tailWord_1191140 prefixEnd_1191140 611627346796574892972053 := by
  unfold tailWord_1191140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21722222452355342680589437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28962963269807123574119249 21722222452355342680589437)
  ·
    refine ⟨8145833419633253505221039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21722222452355342680589437 8145833419633253505221039)
    ·
      refine ⟨12218750129449880257831559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8145833419633253505221039 12218750129449880257831559)
      ·
        refine ⟨18328125194174820386747339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12218750129449880257831559 18328125194174820386747339)
        ·
          refine ⟨27492187791262230580121009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18328125194174820386747339 27492187791262230580121009)
          ·
            refine ⟨20619140843446672935090757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27492187791262230580121009 20619140843446672935090757)
            ·
              refine ⟨3866088908146251175329517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20619140843446672935090757 3866088908146251175329517)
              ·
                refine ⟨1449783340554844190748569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3866088908146251175329517 1449783340554844190748569)
                ·
                  refine ⟨1087337505416133143061427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1449783340554844190748569 1087337505416133143061427)
                  ·
                    refine ⟨1631006258124199714592141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1087337505416133143061427 1631006258124199714592141)
                    ·
                      refine ⟨611627346796574892972053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1631006258124199714592141 611627346796574892972053)
                      ·
                        rfl

theorem cell23_1191140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_1191140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191140 prefixEnd_1191140 := by exact prefixLift 1191140
  have htrace : WordTrace (prefixWord ++ tailWord_1191140) baseStart_1191140 baseEnd_1191140 := by
    simpa [prefixWord, tailWord_1191140, baseEnd_1191140] using wordTrace_append hprefix tailTrace_1191140
  have hstable : (prefixWord ++ tailWord_1191140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191140).length < 2 ^ (prefixWord ++ tailWord_1191140).sum := by decide
  have hdescent : baseEnd_1191140 < baseStart_1191140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191150 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_1191150 : Nat := 118140960795 + 1191150 * 2 ^ 59
def prefixEnd_1191150 : Nat := 4983230072969 + 3 ^ 40 * 1191150 * 2
def baseEnd_1191150 : Nat := 611632481603119853847007

theorem tailTrace_1191150 : CollatzResearch.WordTrace tailWord_1191150 prefixEnd_1191150 611632481603119853847007 := by
  unfold tailWord_1191150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5430601204334307133630363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28963206423116304712695269 5430601204334307133630363)
  ·
    refine ⟨8145901806501460700445545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5430601204334307133630363 8145901806501460700445545)
    ·
      refine ⟨6109426354876095525334159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8145901806501460700445545 6109426354876095525334159)
      ·
        refine ⟨9164139532314143288001239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109426354876095525334159 9164139532314143288001239)
        ·
          refine ⟨13746209298471214932001859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9164139532314143288001239 13746209298471214932001859)
          ·
            refine ⟨20619313947706822398002789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13746209298471214932001859 20619313947706822398002789)
            ·
              refine ⟨3866121365195029199625523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20619313947706822398002789 3866121365195029199625523)
              ·
                refine ⟨5799182047792543799438285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866121365195029199625523 5799182047792543799438285)
                ·
                  refine ⟨2174693267922203924789357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5799182047792543799438285 2174693267922203924789357)
                  ·
                    refine ⟨815509975470826471796009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174693267922203924789357 815509975470826471796009)
                    ·
                      refine ⟨611632481603119853847007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815509975470826471796009 611632481603119853847007)
                      ·
                        rfl

theorem cell23_1191150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_1191150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191150 prefixEnd_1191150 := by exact prefixLift 1191150
  have htrace : WordTrace (prefixWord ++ tailWord_1191150) baseStart_1191150 baseEnd_1191150 := by
    simpa [prefixWord, tailWord_1191150, baseEnd_1191150] using wordTrace_append hprefix tailTrace_1191150
  have hstable : (prefixWord ++ tailWord_1191150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191150).length < 2 ^ (prefixWord ++ tailWord_1191150).sum := by decide
  have hdescent : baseEnd_1191150 < baseStart_1191150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191167 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 1, 3, 2]
def baseStart_1191167 : Nat := 118140960795 + 1191167 * 2 ^ 59
def prefixEnd_1191167 : Nat := 4983230072969 + 3 ^ 40 * 1191167 * 2
def baseEnd_1191167 : Nat := 611641210774246287334429

theorem tailTrace_1191167 : CollatzResearch.WordTrace tailWord_1191167 prefixEnd_1191167 611641210774246287334429 := by
  unfold tailWord_1191167
  simp only [CollatzResearch.WordTrace]
  refine ⟨43445429675612868972411755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28963619783741912648274503 43445429675612868972411755)
  ·
    refine ⟨65168144513419303458617633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43445429675612868972411755 65168144513419303458617633)
    ·
      refine ⟨48876108385064477593963225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65168144513419303458617633 48876108385064477593963225)
      ·
        refine ⟨36657081288798358195472419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48876108385064477593963225 36657081288798358195472419)
        ·
          refine ⟨54985621933197537293208629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36657081288798358195472419 54985621933197537293208629)
          ·
            refine ⟨5154902056237269121238309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54985621933197537293208629 5154902056237269121238309)
            ·
              refine ⟨966544135544487960232183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5154902056237269121238309 966544135544487960232183)
              ·
                refine ⟨1449816203316731940348275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966544135544487960232183 1449816203316731940348275)
                ·
                  refine ⟨2174724304975097910522413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449816203316731940348275 2174724304975097910522413)
                  ·
                    refine ⟨815521614365661716445905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174724304975097910522413 815521614365661716445905)
                    ·
                      refine ⟨611641210774246287334429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815521614365661716445905 611641210774246287334429)
                      ·
                        rfl

theorem cell23_1191167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_1191167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191167 prefixEnd_1191167 := by exact prefixLift 1191167
  have htrace : WordTrace (prefixWord ++ tailWord_1191167) baseStart_1191167 baseEnd_1191167 := by
    simpa [prefixWord, tailWord_1191167, baseEnd_1191167] using wordTrace_append hprefix tailTrace_1191167
  have hstable : (prefixWord ++ tailWord_1191167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191167).length < 2 ^ (prefixWord ++ tailWord_1191167).sum := by decide
  have hdescent : baseEnd_1191167 < baseStart_1191167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191197 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1191197 : Nat := 118140960795 + 1191197 * 2 ^ 59
def prefixEnd_1191197 : Nat := 4983230072969 + 3 ^ 40 * 1191197 * 2
def baseEnd_1191197 : Nat := 611656615193881169959291

theorem tailTrace_1191197 : CollatzResearch.WordTrace tailWord_1191197 prefixEnd_1191197 611656615193881169959291 := by
  unfold tailWord_1191197
  simp only [CollatzResearch.WordTrace]
  refine ⟨43446523865504184096003845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28964349243669456064002563 43446523865504184096003845)
  ·
    refine ⟨8146223224782034518000721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43446523865504184096003845 8146223224782034518000721)
    ·
      refine ⟨6109667418586525888500541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8146223224782034518000721 6109667418586525888500541)
      ·
        refine ⟨2291125281969947208187703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6109667418586525888500541 2291125281969947208187703)
        ·
          refine ⟨3436687922954920812281555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291125281969947208187703 3436687922954920812281555)
          ·
            refine ⟨5155031884432381218422333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436687922954920812281555 5155031884432381218422333)
            ·
              refine ⟨1933136956662142956908375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5155031884432381218422333 1933136956662142956908375)
              ·
                refine ⟨2899705434993214435362563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933136956662142956908375 2899705434993214435362563)
                ·
                  refine ⟨4349558152489821653043845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2899705434993214435362563 4349558152489821653043845)
                  ·
                    refine ⟨815542153591841559945721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4349558152489821653043845 815542153591841559945721)
                    ·
                      refine ⟨611656615193881169959291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815542153591841559945721 611656615193881169959291)
                      ·
                        rfl

theorem cell23_1191197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1191197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191197 prefixEnd_1191197 := by exact prefixLift 1191197
  have htrace : WordTrace (prefixWord ++ tailWord_1191197) baseStart_1191197 baseEnd_1191197 := by
    simpa [prefixWord, tailWord_1191197, baseEnd_1191197] using wordTrace_append hprefix tailTrace_1191197
  have hstable : (prefixWord ++ tailWord_1191197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191197).length < 2 ^ (prefixWord ++ tailWord_1191197).sum := by decide
  have hdescent : baseEnd_1191197 < baseStart_1191197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191216 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_1191216 : Nat := 118140960795 + 1191216 * 2 ^ 59
def prefixEnd_1191216 : Nat := 4983230072969 + 3 ^ 40 * 1191216 * 2
def baseEnd_1191216 : Nat := 203888790442105531873901

theorem tailTrace_1191216 : CollatzResearch.WordTrace tailWord_1191216 prefixEnd_1191216 203888790442105531873901 := by
  unfold tailWord_1191216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21723608426217675170472751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28964811234956900227297001 21723608426217675170472751)
  ·
    refine ⟨32585412639326512755709127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21723608426217675170472751 32585412639326512755709127)
    ·
      refine ⟨48878118958989769133563691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32585412639326512755709127 48878118958989769133563691)
      ·
        refine ⟨73317178438484653700345537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48878118958989769133563691 73317178438484653700345537)
        ·
          refine ⟨54987883828863490275259153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73317178438484653700345537 54987883828863490275259153)
          ·
            refine ⟨41240912871647617706444365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54987883828863490275259153 41240912871647617706444365)
            ·
              refine ⟨15465342326867856639916637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41240912871647617706444365 15465342326867856639916637)
              ·
                refine ⟨5799503372575446239968739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15465342326867856639916637 5799503372575446239968739)
                ·
                  refine ⟨8699255058863169359953109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5799503372575446239968739 8699255058863169359953109)
                  ·
                    refine ⟨203888790442105531873901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8699255058863169359953109 203888790442105531873901)
                    ·
                      rfl

theorem cell23_1191216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_1191216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191216 prefixEnd_1191216 := by exact prefixLift 1191216
  have htrace : WordTrace (prefixWord ++ tailWord_1191216) baseStart_1191216 baseEnd_1191216 := by
    simpa [prefixWord, tailWord_1191216, baseEnd_1191216] using wordTrace_append hprefix tailTrace_1191216
  have hstable : (prefixWord ++ tailWord_1191216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191216).length < 2 ^ (prefixWord ++ tailWord_1191216).sum := by decide
  have hdescent : baseEnd_1191216 < baseStart_1191216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191223 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_1191223 : Nat := 118140960795 + 1191223 * 2 ^ 59
def prefixEnd_1191223 : Nat := 4983230072969 + 3 ^ 40 * 1191223 * 2
def baseEnd_1191223 : Nat := 611669965690898068234171

theorem tailTrace_1191223 : CollatzResearch.WordTrace tailWord_1191223 prefixEnd_1191223 611669965690898068234171 := by
  unfold tailWord_1191223
  simp only [CollatzResearch.WordTrace]
  refine ⟨43447472163409990536450323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28964981442273327024300215 43447472163409990536450323)
  ·
    refine ⟨65171208245114985804675485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43447472163409990536450323 65171208245114985804675485)
    ·
      refine ⟨24439203091918119676753307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65171208245114985804675485 24439203091918119676753307)
      ·
        refine ⟨36658804637877179515129961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24439203091918119676753307 36658804637877179515129961)
        ·
          refine ⟨27494103478407884636347471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36658804637877179515129961 27494103478407884636347471)
          ·
            refine ⟨41241155217611826954521207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27494103478407884636347471 41241155217611826954521207)
            ·
              refine ⟨61861732826417740431781811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41241155217611826954521207 61861732826417740431781811)
              ·
                refine ⟨92792599239626610647672717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61861732826417740431781811 92792599239626610647672717)
                ·
                  refine ⟨34797224714859978992877269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92792599239626610647672717 34797224714859978992877269)
                  ·
                    refine ⟨815559954254530757645561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34797224714859978992877269 815559954254530757645561)
                    ·
                      refine ⟨611669965690898068234171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815559954254530757645561 611669965690898068234171)
                      ·
                        rfl

theorem cell23_1191223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_1191223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191223 prefixEnd_1191223 := by exact prefixLift 1191223
  have htrace : WordTrace (prefixWord ++ tailWord_1191223) baseStart_1191223 baseEnd_1191223 := by
    simpa [prefixWord, tailWord_1191223, baseEnd_1191223] using wordTrace_append hprefix tailTrace_1191223
  have hstable : (prefixWord ++ tailWord_1191223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191223).length < 2 ^ (prefixWord ++ tailWord_1191223).sum := by decide
  have hdescent : baseEnd_1191223 < baseStart_1191223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191263 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 5, 4]
def baseStart_1191263 : Nat := 118140960795 + 1191263 * 2 ^ 59
def prefixEnd_1191263 : Nat := 4983230072969 + 3 ^ 40 * 1191263 * 2
def baseEnd_1191263 : Nat := 203896834972359303911329

theorem tailTrace_1191263 : CollatzResearch.WordTrace tailWord_1191263 prefixEnd_1191263 203896834972359303911329 := by
  unfold tailWord_1191263
  simp only [CollatzResearch.WordTrace]
  refine ⟨43448931083265077367906443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28965954055510051578604295 43448931083265077367906443)
  ·
    refine ⟨65173396624897616051859665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43448931083265077367906443 65173396624897616051859665)
    ·
      refine ⟨48880047468673212038894749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65173396624897616051859665 48880047468673212038894749)
      ·
        refine ⟨18330017800752454514585531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48880047468673212038894749 18330017800752454514585531)
        ·
          refine ⟨27495026701128681771878297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18330017800752454514585531 27495026701128681771878297)
          ·
            refine ⟨20621270025846511328908723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27495026701128681771878297 20621270025846511328908723)
            ·
              refine ⟨30931905038769766993363085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20621270025846511328908723 30931905038769766993363085)
              ·
                refine ⟨11599464389538662622511157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30931905038769766993363085 11599464389538662622511157)
                ·
                  refine ⟨1087449786519249620860421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11599464389538662622511157 1087449786519249620860421)
                  ·
                    refine ⟨203896834972359303911329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087449786519249620860421 203896834972359303911329)
                    ·
                      rfl

theorem cell23_1191263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_1191263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191263 prefixEnd_1191263 := by exact prefixLift 1191263
  have htrace : WordTrace (prefixWord ++ tailWord_1191263) baseStart_1191263 baseEnd_1191263 := by
    simpa [prefixWord, tailWord_1191263, baseEnd_1191263] using wordTrace_append hprefix tailTrace_1191263
  have hstable : (prefixWord ++ tailWord_1191263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191263).length < 2 ^ (prefixWord ++ tailWord_1191263).sum := by decide
  have hdescent : baseEnd_1191263 < baseStart_1191263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191314 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1191314 : Nat := 118140960795 + 1191314 * 2 ^ 59
def prefixEnd_1191314 : Nat := 4983230072969 + 3 ^ 40 * 1191314 * 2
def baseEnd_1191314 : Nat := 203905564143485737398751

theorem tailTrace_1191314 : CollatzResearch.WordTrace tailWord_1191314 prefixEnd_1191314 203905564143485737398751 := by
  unfold tailWord_1191314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10862697801520078269503249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28967194137386875385341997 10862697801520078269503249)
  ·
    refine ⟨8147023351140058702127437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10862697801520078269503249 8147023351140058702127437)
    ·
      refine ⟨3055133756677522013297789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8147023351140058702127437 3055133756677522013297789)
      ·
        refine ⟨1145675158754070754986671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3055133756677522013297789 1145675158754070754986671)
        ·
          refine ⟨1718512738131106132480007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145675158754070754986671 1718512738131106132480007)
          ·
            refine ⟨2577769107196659198720011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718512738131106132480007 2577769107196659198720011)
            ·
              refine ⟨3866653660794988798080017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577769107196659198720011 3866653660794988798080017)
              ·
                refine ⟨2899990245596241598560013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866653660794988798080017 2899990245596241598560013)
                ·
                  refine ⟨1087496342098590599460005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2899990245596241598560013 1087496342098590599460005)
                  ·
                    refine ⟨203905564143485737398751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087496342098590599460005 203905564143485737398751)
                    ·
                      rfl

theorem cell23_1191314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1191314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191314 prefixEnd_1191314 := by exact prefixLift 1191314
  have htrace : WordTrace (prefixWord ++ tailWord_1191314) baseStart_1191314 baseEnd_1191314 := by
    simpa [prefixWord, tailWord_1191314, baseEnd_1191314] using wordTrace_append hprefix tailTrace_1191314
  have hstable : (prefixWord ++ tailWord_1191314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191314).length < 2 ^ (prefixWord ++ tailWord_1191314).sum := by decide
  have hdescent : baseEnd_1191314 < baseStart_1191314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191363 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5]
def baseStart_1191363 : Nat := 118140960795 + 1191363 * 2 ^ 59
def prefixEnd_1191363 : Nat := 4983230072969 + 3 ^ 40 * 1191363 * 2
def baseEnd_1191363 : Nat := 611741852982527520483527

theorem tailTrace_1191363 : CollatzResearch.WordTrace tailWord_1191363 prefixEnd_1191363 611741852982527520483527 := by
  unfold tailWord_1191363
  simp only [CollatzResearch.WordTrace]
  refine ⟨43452578382902794446546743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28968385588601862964364495 43452578382902794446546743)
  ·
    refine ⟨65178867574354191669820115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43452578382902794446546743 65178867574354191669820115)
    ·
      refine ⟨97768301361531287504730173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65178867574354191669820115 97768301361531287504730173)
      ·
        refine ⟨36663113010574232814273815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97768301361531287504730173 36663113010574232814273815)
        ·
          refine ⟨54994669515861349221410723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36663113010574232814273815 54994669515861349221410723)
          ·
            refine ⟨82492004273792023832116085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54994669515861349221410723 82492004273792023832116085)
            ·
              refine ⟨7733625400668002234260883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82492004273792023832116085 7733625400668002234260883)
              ·
                refine ⟨11600438101002003351391325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7733625400668002234260883 11600438101002003351391325)
                ·
                  refine ⟨4350164287875751256771747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11600438101002003351391325 4350164287875751256771747)
                  ·
                    refine ⟨6525246431813626885157621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350164287875751256771747 6525246431813626885157621)
                    ·
                      refine ⟨611741852982527520483527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6525246431813626885157621 611741852982527520483527)
                      ·
                        rfl

theorem cell23_1191363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_1191363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191363 prefixEnd_1191363 := by exact prefixLift 1191363
  have htrace : WordTrace (prefixWord ++ tailWord_1191363) baseStart_1191363 baseEnd_1191363 := by
    simpa [prefixWord, tailWord_1191363, baseEnd_1191363] using wordTrace_append hprefix tailTrace_1191363
  have hstable : (prefixWord ++ tailWord_1191363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191363).length < 2 ^ (prefixWord ++ tailWord_1191363).sum := by decide
  have hdescent : baseEnd_1191363 < baseStart_1191363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191370 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_1191370 : Nat := 118140960795 + 1191370 * 2 ^ 59
def prefixEnd_1191370 : Nat := 4983230072969 + 3 ^ 40 * 1191370 * 2
def baseEnd_1191370 : Nat := 203915149115702997698665

theorem tailTrace_1191370 : CollatzResearch.WordTrace tailWord_1191370 prefixEnd_1191370 203915149115702997698665 := by
  unfold tailWord_1191370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863208423469358660512891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28968555795918289761367709 10863208423469358660512891)
  ·
    refine ⟨16294812635204037990769337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10863208423469358660512891 16294812635204037990769337)
    ·
      refine ⟨12221109476403028493077003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16294812635204037990769337 12221109476403028493077003)
      ·
        refine ⟨18331664214604542739615505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12221109476403028493077003 18331664214604542739615505)
        ·
          refine ⟨13748748160953407054711629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18331664214604542739615505 13748748160953407054711629)
          ·
            refine ⟨5155780560357527645516861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13748748160953407054711629 5155780560357527645516861)
            ·
              refine ⟨1933417710134072867068823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5155780560357527645516861 1933417710134072867068823)
              ·
                refine ⟨2900126565201109300603235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933417710134072867068823 2900126565201109300603235)
                ·
                  refine ⟨4350189847801663950904853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900126565201109300603235 4350189847801663950904853)
                  ·
                    refine ⟨203915149115702997698665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4350189847801663950904853 203915149115702997698665)
                    ·
                      rfl

theorem cell23_1191370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_1191370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191370 prefixEnd_1191370 := by exact prefixLift 1191370
  have htrace : WordTrace (prefixWord ++ tailWord_1191370) baseStart_1191370 baseEnd_1191370 := by
    simpa [prefixWord, tailWord_1191370, baseEnd_1191370] using wordTrace_append hprefix tailTrace_1191370
  have hstable : (prefixWord ++ tailWord_1191370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191370).length < 2 ^ (prefixWord ++ tailWord_1191370).sum := by decide
  have hdescent : baseEnd_1191370 < baseStart_1191370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191397 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1191397 : Nat := 118140960795 + 1191397 * 2 ^ 59
def prefixEnd_1191397 : Nat := 4983230072969 + 3 ^ 40 * 1191397 * 2
def baseEnd_1191397 : Nat := 611759311324780387458371

theorem tailTrace_1191397 : CollatzResearch.WordTrace tailWord_1191397 prefixEnd_1191397 611759311324780387458371 := by
  unfold tailWord_1191397
  simp only [CollatzResearch.WordTrace]
  refine ⟨43453818464779618253284445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28969212309853078835522963 43453818464779618253284445)
  ·
    refine ⟨16295181924292356844981667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43453818464779618253284445 16295181924292356844981667)
    ·
      refine ⟨24442772886438535267472501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16295181924292356844981667 24442772886438535267472501)
      ·
        refine ⟨2291509958103612681325547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24442772886438535267472501 2291509958103612681325547)
        ·
          refine ⟨3437264937155419021988321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291509958103612681325547 3437264937155419021988321)
          ·
            refine ⟨2577948702866564266491241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3437264937155419021988321 2577948702866564266491241)
            ·
              refine ⟨1933461527149923199868431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577948702866564266491241 1933461527149923199868431)
              ·
                refine ⟨2900192290724884799802647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933461527149923199868431 2900192290724884799802647)
                ·
                  refine ⟨4350288436087327199703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900192290724884799802647 4350288436087327199703971)
                  ·
                    refine ⟨6525432654130990799555957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4350288436087327199703971 6525432654130990799555957)
                    ·
                      refine ⟨611759311324780387458371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6525432654130990799555957 611759311324780387458371)
                      ·
                        rfl

theorem cell23_1191397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1191397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191397 prefixEnd_1191397 := by exact prefixLift 1191397
  have htrace : WordTrace (prefixWord ++ tailWord_1191397) baseStart_1191397 baseEnd_1191397 := by
    simpa [prefixWord, tailWord_1191397, baseEnd_1191397] using wordTrace_append hprefix tailTrace_1191397
  have hstable : (prefixWord ++ tailWord_1191397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191397).length < 2 ^ (prefixWord ++ tailWord_1191397).sum := by decide
  have hdescent : baseEnd_1191397 < baseStart_1191397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191423 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1191423 : Nat := 118140960795 + 1191423 * 2 ^ 59
def prefixEnd_1191423 : Nat := 4983230072969 + 3 ^ 40 * 1191423 * 2
def baseEnd_1191423 : Nat := 611772661821797285733251

theorem tailTrace_1191423 : CollatzResearch.WordTrace tailWord_1191423 prefixEnd_1191423 611772661821797285733251 := by
  unfold tailWord_1191423
  simp only [CollatzResearch.WordTrace]
  refine ⟨43454766762685424693730923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28969844508456949795820615 43454766762685424693730923)
  ·
    refine ⟨65182150144028137040596385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43454766762685424693730923 65182150144028137040596385)
    ·
      refine ⟨48886612608021102780447289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65182150144028137040596385 48886612608021102780447289)
      ·
        refine ⟨36664959456015827085335467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48886612608021102780447289 36664959456015827085335467)
        ·
          refine ⟨54997439184023740628003201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36664959456015827085335467 54997439184023740628003201)
          ·
            refine ⟨41248079388017805471002401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54997439184023740628003201 41248079388017805471002401)
            ·
              refine ⟨30936059541013354103251801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41248079388017805471002401 30936059541013354103251801)
              ·
                refine ⟨23202044655760015577438851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30936059541013354103251801 23202044655760015577438851)
                ·
                  refine ⟨34803066983640023366158277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23202044655760015577438851 34803066983640023366158277)
                  ·
                    refine ⟨6525575059432504381154677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34803066983640023366158277 6525575059432504381154677)
                    ·
                      refine ⟨611772661821797285733251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6525575059432504381154677 611772661821797285733251)
                      ·
                        rfl

theorem cell23_1191423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1191423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191423 prefixEnd_1191423 := by exact prefixLift 1191423
  have htrace : WordTrace (prefixWord ++ tailWord_1191423) baseStart_1191423 baseEnd_1191423 := by
    simpa [prefixWord, tailWord_1191423, baseEnd_1191423] using wordTrace_append hprefix tailTrace_1191423
  have hstable : (prefixWord ++ tailWord_1191423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191423).length < 2 ^ (prefixWord ++ tailWord_1191423).sum := by decide
  have hdescent : baseEnd_1191423 < baseStart_1191423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191480 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1191480 : Nat := 118140960795 + 1191480 * 2 ^ 59
def prefixEnd_1191480 : Nat := 4983230072969 + 3 ^ 40 * 1191480 * 2
def baseEnd_1191480 : Nat := 611801930219103562720489

theorem tailTrace_1191480 : CollatzResearch.WordTrace tailWord_1191480 prefixEnd_1191480 611801930219103562720489 := by
  unfold tailWord_1191480
  simp only [CollatzResearch.WordTrace]
  refine ⟨21728422861739461714277947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28971230482319282285703929 21728422861739461714277947)
  ·
    refine ⟨32592634292609192571416921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21728422861739461714277947 32592634292609192571416921)
    ·
      refine ⟨24444475719456894428562691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32592634292609192571416921 24444475719456894428562691)
      ·
        refine ⟨36666713579185341642844037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24444475719456894428562691 36666713579185341642844037)
        ·
          refine ⟨6875008796097251558033257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36666713579185341642844037 6875008796097251558033257)
          ·
            refine ⟨5156256597072938668524943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6875008796097251558033257 5156256597072938668524943)
            ·
              refine ⟨7734384895609408002787415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156256597072938668524943 7734384895609408002787415)
              ·
                refine ⟨11601577343414112004181123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7734384895609408002787415 11601577343414112004181123)
                ·
                  refine ⟨17402366015121168006271685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11601577343414112004181123 17402366015121168006271685)
                  ·
                    refine ⟨3262943627835219001175941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17402366015121168006271685 3262943627835219001175941)
                    ·
                      refine ⟨611801930219103562720489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3262943627835219001175941 611801930219103562720489)
                      ·
                        rfl

theorem cell23_1191480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1191480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191480 prefixEnd_1191480 := by exact prefixLift 1191480
  have htrace : WordTrace (prefixWord ++ tailWord_1191480) baseStart_1191480 baseEnd_1191480 := by
    simpa [prefixWord, tailWord_1191480, baseEnd_1191480] using wordTrace_append hprefix tailTrace_1191480
  have hstable : (prefixWord ++ tailWord_1191480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191480).length < 2 ^ (prefixWord ++ tailWord_1191480).sum := by decide
  have hdescent : baseEnd_1191480 < baseStart_1191480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191520 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_1191520 : Nat := 118140960795 + 1191520 * 2 ^ 59
def prefixEnd_1191520 : Nat := 4983230072969 + 3 ^ 40 * 1191520 * 2
def baseEnd_1191520 : Nat := 203940823148427802073435

theorem tailTrace_1191520 : CollatzResearch.WordTrace tailWord_1191520 prefixEnd_1191520 203940823148427802073435 := by
  unfold tailWord_1191520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21729152321667005130006007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28972203095556006840008009 21729152321667005130006007)
  ·
    refine ⟨32593728482500507695009011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21729152321667005130006007 32593728482500507695009011)
    ·
      refine ⟨48890592723750761542513517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32593728482500507695009011 48890592723750761542513517)
      ·
        refine ⟨18333972271406535578442569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48890592723750761542513517 18333972271406535578442569)
        ·
          refine ⟨13750479203554901683831927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18333972271406535578442569 13750479203554901683831927)
          ·
            refine ⟨20625718805332352525747891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13750479203554901683831927 20625718805332352525747891)
            ·
              refine ⟨30938578207998528788621837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20625718805332352525747891 30938578207998528788621837)
              ·
                refine ⟨11601966827999448295733189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30938578207998528788621837 11601966827999448295733189)
                ·
                  refine ⟨2175368780249896555449973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11601966827999448295733189 2175368780249896555449973)
                  ·
                    refine ⟨203940823148427802073435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2175368780249896555449973 203940823148427802073435)
                    ·
                      rfl

theorem cell23_1191520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_1191520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191520 prefixEnd_1191520 := by exact prefixLift 1191520
  have htrace : WordTrace (prefixWord ++ tailWord_1191520) baseStart_1191520 baseEnd_1191520 := by
    simpa [prefixWord, tailWord_1191520, baseEnd_1191520] using wordTrace_append hprefix tailTrace_1191520
  have hstable : (prefixWord ++ tailWord_1191520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191520).length < 2 ^ (prefixWord ++ tailWord_1191520).sum := by decide
  have hdescent : baseEnd_1191520 < baseStart_1191520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191527 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_1191527 : Nat := 118140960795 + 1191527 * 2 ^ 59
def prefixEnd_1191527 : Nat := 4983230072969 + 3 ^ 40 * 1191527 * 2
def baseEnd_1191527 : Nat := 611826063809864878832773

theorem tailTrace_1191527 : CollatzResearch.WordTrace tailWord_1191527 prefixEnd_1191527 611826063809864878832773 := by
  unfold tailWord_1191527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43458559954308650455516835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28972373302872433637011223 43458559954308650455516835)
  ·
    refine ⟨65187839931462975683275253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43458559954308650455516835 65187839931462975683275253)
    ·
      refine ⟨6111359993574653970307055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65187839931462975683275253 6111359993574653970307055)
      ·
        refine ⟨9167039990361980955460583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111359993574653970307055 9167039990361980955460583)
        ·
          refine ⟨13750559985542971433190875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9167039990361980955460583 13750559985542971433190875)
          ·
            refine ⟨20625839978314457149786313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13750559985542971433190875 20625839978314457149786313)
            ·
              refine ⟨15469379983735842862339735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20625839978314457149786313 15469379983735842862339735)
              ·
                refine ⟨23204069975603764293509603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15469379983735842862339735 23204069975603764293509603)
                ·
                  refine ⟨34806104963405646440264405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23204069975603764293509603 34806104963405646440264405)
                  ·
                    refine ⟨815768085079819838443697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34806104963405646440264405 815768085079819838443697)
                    ·
                      refine ⟨611826063809864878832773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815768085079819838443697 611826063809864878832773)
                      ·
                        rfl

theorem cell23_1191527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_1191527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191527 prefixEnd_1191527 := by exact prefixLift 1191527
  have htrace : WordTrace (prefixWord ++ tailWord_1191527) baseStart_1191527 baseEnd_1191527 := by
    simpa [prefixWord, tailWord_1191527, baseEnd_1191527] using wordTrace_append hprefix tailTrace_1191527
  have hstable : (prefixWord ++ tailWord_1191527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191527).length < 2 ^ (prefixWord ++ tailWord_1191527).sum := by decide
  have hdescent : baseEnd_1191527 < baseStart_1191527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191557 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_1191557 : Nat := 118140960795 + 1191557 * 2 ^ 59
def prefixEnd_1191557 : Nat := 4983230072969 + 3 ^ 40 * 1191557 * 2
def baseEnd_1191557 : Nat := 611841468229499761457635

theorem tailTrace_1191557 : CollatzResearch.WordTrace tailWord_1191557 prefixEnd_1191557 611841468229499761457635 := by
  unfold tailWord_1191557
  simp only [CollatzResearch.WordTrace]
  refine ⟨43459654144199965579108925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28973102762799977052739283 43459654144199965579108925)
  ·
    refine ⟨16297370304074987092165847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43459654144199965579108925 16297370304074987092165847)
    ·
      refine ⟨24446055456112480638248771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16297370304074987092165847 24446055456112480638248771)
      ·
        refine ⟨36669083184168720957373157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24446055456112480638248771 36669083184168720957373157)
        ·
          refine ⟨6875453097031635179507467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36669083184168720957373157 6875453097031635179507467)
          ·
            refine ⟨10313179645547452769261201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6875453097031635179507467 10313179645547452769261201)
            ·
              refine ⟨7734884734160589576945901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10313179645547452769261201 7734884734160589576945901)
              ·
                refine ⟨2900581775310221091354713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7734884734160589576945901 2900581775310221091354713)
                ·
                  refine ⟨2175436331482665818516035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900581775310221091354713 2175436331482665818516035)
                  ·
                    refine ⟨3263154497223998727774053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2175436331482665818516035 3263154497223998727774053)
                    ·
                      refine ⟨611841468229499761457635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3263154497223998727774053 611841468229499761457635)
                      ·
                        rfl

theorem cell23_1191557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_1191557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191557 prefixEnd_1191557 := by exact prefixLift 1191557
  have htrace : WordTrace (prefixWord ++ tailWord_1191557) baseStart_1191557 baseEnd_1191557 := by
    simpa [prefixWord, tailWord_1191557, baseEnd_1191557] using wordTrace_append hprefix tailTrace_1191557
  have hstable : (prefixWord ++ tailWord_1191557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191557).length < 2 ^ (prefixWord ++ tailWord_1191557).sum := by decide
  have hdescent : baseEnd_1191557 < baseStart_1191557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191584 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_1191584 : Nat := 118140960795 + 1191584 * 2 ^ 59
def prefixEnd_1191584 : Nat := 4983230072969 + 3 ^ 40 * 1191584 * 2
def baseEnd_1191584 : Nat := 203951777402390385273337

theorem tailTrace_1191584 : CollatzResearch.WordTrace tailWord_1191584 prefixEnd_1191584 203951777402390385273337 := by
  unfold tailWord_1191584
  simp only [CollatzResearch.WordTrace]
  refine ⟨21730319457551074595170903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28973759276734766126894537 21730319457551074595170903)
  ·
    refine ⟨32595479186326611892756355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21730319457551074595170903 32595479186326611892756355)
    ·
      refine ⟨48893218779489917839134533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32595479186326611892756355 48893218779489917839134533)
      ·
        refine ⟨9167478521154359594837725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48893218779489917839134533 9167478521154359594837725)
        ·
          refine ⟨3437804445432884848064147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9167478521154359594837725 3437804445432884848064147)
          ·
            refine ⟨5156706668149327272096221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437804445432884848064147 5156706668149327272096221)
            ·
              refine ⟨1933765000555997727036083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5156706668149327272096221 1933765000555997727036083)
              ·
                refine ⟨2900647500833996590554125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933765000555997727036083 2900647500833996590554125)
                ·
                  refine ⟨1087742812812748721457797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2900647500833996590554125 1087742812812748721457797)
                  ·
                    refine ⟨203951777402390385273337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087742812812748721457797 203951777402390385273337)
                    ·
                      rfl

theorem cell23_1191584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_1191584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191584 prefixEnd_1191584 := by exact prefixLift 1191584
  have htrace : WordTrace (prefixWord ++ tailWord_1191584) baseStart_1191584 baseEnd_1191584 := by
    simpa [prefixWord, tailWord_1191584, baseEnd_1191584] using wordTrace_append hprefix tailTrace_1191584
  have hstable : (prefixWord ++ tailWord_1191584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191584).length < 2 ^ (prefixWord ++ tailWord_1191584).sum := by decide
  have hdescent : baseEnd_1191584 < baseStart_1191584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191600 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_1191600 : Nat := 118140960795 + 1191600 * 2 ^ 59
def prefixEnd_1191600 : Nat := 4983230072969 + 3 ^ 40 * 1191600 * 2
def baseEnd_1191600 : Nat := 611863547897643093219937

theorem tailTrace_1191600 : CollatzResearch.WordTrace tailWord_1191600 prefixEnd_1191600 611863547897643093219937 := by
  unfold tailWord_1191600
  simp only [CollatzResearch.WordTrace]
  refine ⟨21730611241522091961462127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28974148322029455948616169 21730611241522091961462127)
  ·
    refine ⟨32595916862283137942193191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21730611241522091961462127 32595916862283137942193191)
    ·
      refine ⟨48893875293424706913289787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32595916862283137942193191 48893875293424706913289787)
      ·
        refine ⟨73340812940137060369934681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48893875293424706913289787 73340812940137060369934681)
        ·
          refine ⟨55005609705102795277451011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73340812940137060369934681 55005609705102795277451011)
          ·
            refine ⟨82508414557654192916176517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55005609705102795277451011 82508414557654192916176517)
            ·
              refine ⟨15470327729560161171783097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82508414557654192916176517 15470327729560161171783097)
              ·
                refine ⟨11602745797170120878837323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15470327729560161171783097 11602745797170120878837323)
                ·
                  refine ⟨17404118695755181318255985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11602745797170120878837323 17404118695755181318255985)
                  ·
                    refine ⟨13053089021816385988691989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17404118695755181318255985 13053089021816385988691989)
                    ·
                      refine ⟨611863547897643093219937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13053089021816385988691989 611863547897643093219937)
                      ·
                        rfl

theorem cell23_1191600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_1191600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191600 prefixEnd_1191600 := by exact prefixLift 1191600
  have htrace : WordTrace (prefixWord ++ tailWord_1191600) baseStart_1191600 baseEnd_1191600 := by
    simpa [prefixWord, tailWord_1191600, baseEnd_1191600] using wordTrace_append hprefix tailTrace_1191600
  have hstable : (prefixWord ++ tailWord_1191600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191600).length < 2 ^ (prefixWord ++ tailWord_1191600).sum := by decide
  have hdescent : baseEnd_1191600 < baseStart_1191600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191627 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 1, 5]
def baseStart_1191627 : Nat := 118140960795 + 1191627 * 2 ^ 59
def prefixEnd_1191627 : Nat := 4983230072969 + 3 ^ 40 * 1191627 * 2
def baseEnd_1191627 : Nat := 203959137291771495860771

theorem tailTrace_1191627 : CollatzResearch.WordTrace tailWord_1191627 prefixEnd_1191627 203959137291771495860771 := by
  unfold tailWord_1191627
  simp only [CollatzResearch.WordTrace]
  refine ⟨43462207253946367534157135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28974804835964245022771423 43462207253946367534157135)
  ·
    refine ⟨65193310880919551301235703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43462207253946367534157135 65193310880919551301235703)
    ·
      refine ⟨97789966321379326951853555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65193310880919551301235703 97789966321379326951853555)
      ·
        refine ⟨146684949482068990427780333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97789966321379326951853555 146684949482068990427780333)
        ·
          refine ⟨55006856055775871410417625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146684949482068990427780333 55006856055775871410417625)
          ·
            refine ⟨41255142041831903557813219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55006856055775871410417625 41255142041831903557813219)
            ·
              refine ⟨61882713062747855336719829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41255142041831903557813219 61882713062747855336719829)
              ·
                refine ⟨1450376087408152859454371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61882713062747855336719829 1450376087408152859454371)
                ·
                  refine ⟨2175564131112229289181557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450376087408152859454371 2175564131112229289181557)
                  ·
                    refine ⟨203959137291771495860771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2175564131112229289181557 203959137291771495860771)
                    ·
                      rfl

theorem cell23_1191627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 5].length) (baseStart_1191627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191627 prefixEnd_1191627 := by exact prefixLift 1191627
  have htrace : WordTrace (prefixWord ++ tailWord_1191627) baseStart_1191627 baseEnd_1191627 := by
    simpa [prefixWord, tailWord_1191627, baseEnd_1191627] using wordTrace_append hprefix tailTrace_1191627
  have hstable : (prefixWord ++ tailWord_1191627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191627).length < 2 ^ (prefixWord ++ tailWord_1191627).sum := by decide
  have hdescent : baseEnd_1191627 < baseStart_1191627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191647 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1191647 : Nat := 118140960795 + 1191647 * 2 ^ 59
def prefixEnd_1191647 : Nat := 4983230072969 + 3 ^ 40 * 1191647 * 2
def baseEnd_1191647 : Nat := 611887681488404409332221

theorem tailTrace_1191647 : CollatzResearch.WordTrace tailWord_1191647 prefixEnd_1191647 611887681488404409332221 := by
  unfold tailWord_1191647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43462936713873910949885195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28975291142582607299923463 43462936713873910949885195)
  ·
    refine ⟨65194405070810866424827793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43462936713873910949885195 65194405070810866424827793)
    ·
      refine ⟨48895803803108149818620845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65194405070810866424827793 48895803803108149818620845)
      ·
        refine ⟨18335926426165556181982817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48895803803108149818620845 18335926426165556181982817)
        ·
          refine ⟨13751944819624167136487113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18335926426165556181982817 13751944819624167136487113)
          ·
            refine ⟨10313958614718125352365335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13751944819624167136487113 10313958614718125352365335)
            ·
              refine ⟨15470937922077188028548003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10313958614718125352365335 15470937922077188028548003)
              ·
                refine ⟨23206406883115782042822005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15470937922077188028548003 23206406883115782042822005)
                ·
                  refine ⟨2175600645292104566514563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23206406883115782042822005 2175600645292104566514563)
                  ·
                    refine ⟨3263400967938156849771845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2175600645292104566514563 3263400967938156849771845)
                    ·
                      refine ⟨611887681488404409332221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3263400967938156849771845 611887681488404409332221)
                      ·
                        rfl

theorem cell23_1191647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1191647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191647 prefixEnd_1191647 := by exact prefixLift 1191647
  have htrace : WordTrace (prefixWord ++ tailWord_1191647) baseStart_1191647 baseEnd_1191647 := by
    simpa [prefixWord, tailWord_1191647, baseEnd_1191647] using wordTrace_append hprefix tailTrace_1191647
  have hstable : (prefixWord ++ tailWord_1191647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191647).length < 2 ^ (prefixWord ++ tailWord_1191647).sum := by decide
  have hdescent : baseEnd_1191647 < baseStart_1191647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191657 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_1191657 : Nat := 118140960795 + 1191657 * 2 ^ 59
def prefixEnd_1191657 : Nat := 4983230072969 + 3 ^ 40 * 1191657 * 2
def baseEnd_1191657 : Nat := 203964272098316456735725

theorem tailTrace_1191657 : CollatzResearch.WordTrace tailWord_1191657 prefixEnd_1191657 203964272098316456735725 := by
  unfold tailWord_1191657
  simp only [CollatzResearch.WordTrace]
  refine ⟨43463301443837682657749225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28975534295891788438499483 43463301443837682657749225)
  ·
    refine ⟨32597476082878261993311919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43463301443837682657749225 32597476082878261993311919)
    ·
      refine ⟨48896214124317392989967879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32597476082878261993311919 48896214124317392989967879)
      ·
        refine ⟨73344321186476089484951819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48896214124317392989967879 73344321186476089484951819)
        ·
          refine ⟨110016481779714134227427729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73344321186476089484951819 110016481779714134227427729)
          ·
            refine ⟨82512361334785600670570797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110016481779714134227427729 82512361334785600670570797)
            ·
              refine ⟨30942135500544600251464049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82512361334785600670570797 30942135500544600251464049)
              ·
                refine ⟨23206601625408450188598037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30942135500544600251464049 23206601625408450188598037)
                ·
                  refine ⟨1087809451191021102590533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23206601625408450188598037 1087809451191021102590533)
                  ·
                    refine ⟨203964272098316456735725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1087809451191021102590533 203964272098316456735725)
                    ·
                      rfl

theorem cell23_1191657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_1191657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191657 prefixEnd_1191657 := by exact prefixLift 1191657
  have htrace : WordTrace (prefixWord ++ tailWord_1191657) baseStart_1191657 baseEnd_1191657 := by
    simpa [prefixWord, tailWord_1191657, baseEnd_1191657] using wordTrace_append hprefix tailTrace_1191657
  have hstable : (prefixWord ++ tailWord_1191657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191657).length < 2 ^ (prefixWord ++ tailWord_1191657).sum := by decide
  have hdescent : baseEnd_1191657 < baseStart_1191657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191677 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1191677 : Nat := 118140960795 + 1191677 * 2 ^ 59
def prefixEnd_1191677 : Nat := 4983230072969 + 3 ^ 40 * 1191677 * 2
def baseEnd_1191677 : Nat := 611903085908039291957083

theorem tailTrace_1191677 : CollatzResearch.WordTrace tailWord_1191677 prefixEnd_1191677 611903085908039291957083 := by
  unfold tailWord_1191677
  simp only [CollatzResearch.WordTrace]
  refine ⟨43464030903765226073477285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28976020602510150715651523 43464030903765226073477285)
  ·
    refine ⟨8149505794455979888776991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43464030903765226073477285 8149505794455979888776991)
    ·
      refine ⟨12224258691683969833165487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8149505794455979888776991 12224258691683969833165487)
      ·
        refine ⟨18336388037525954749748231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12224258691683969833165487 18336388037525954749748231)
        ·
          refine ⟨27504582056288932124622347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336388037525954749748231 27504582056288932124622347)
          ·
            refine ⟨41256873084433398186933521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27504582056288932124622347 41256873084433398186933521)
            ·
              refine ⟨30942654813325048640200141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41256873084433398186933521 30942654813325048640200141)
              ·
                refine ⟨11603495554996893240075053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30942654813325048640200141 11603495554996893240075053)
                ·
                  refine ⟨4351310833123834965028145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11603495554996893240075053 4351310833123834965028145)
                  ·
                    refine ⟨3263483124842876223771109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4351310833123834965028145 3263483124842876223771109)
                    ·
                      refine ⟨611903085908039291957083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3263483124842876223771109 611903085908039291957083)
                      ·
                        rfl

theorem cell23_1191677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1191677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191677 prefixEnd_1191677 := by exact prefixLift 1191677
  have htrace : WordTrace (prefixWord ++ tailWord_1191677) baseStart_1191677 baseEnd_1191677 := by
    simpa [prefixWord, tailWord_1191677, baseEnd_1191677] using wordTrace_append hprefix tailTrace_1191677
  have hstable : (prefixWord ++ tailWord_1191677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191677).length < 2 ^ (prefixWord ++ tailWord_1191677).sum := by decide
  have hdescent : baseEnd_1191677 < baseStart_1191677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191681 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_1191681 : Nat := 118140960795 + 1191681 * 2 ^ 59
def prefixEnd_1191681 : Nat := 4983230072969 + 3 ^ 40 * 1191681 * 2
def baseEnd_1191681 : Nat := 611905139830657276307065

theorem tailTrace_1191681 : CollatzResearch.WordTrace tailWord_1191681 prefixEnd_1191681 611905139830657276307065 := by
  unfold tailWord_1191681
  simp only [CollatzResearch.WordTrace]
  refine ⟨43464176795750734756622897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28976117863833823171081931 43464176795750734756622897)
  ·
    refine ⟨32598132596813051067467173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43464176795750734756622897 32598132596813051067467173)
    ·
      refine ⟨6112149861902447075150095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32598132596813051067467173 6112149861902447075150095)
      ·
        refine ⟨9168224792853670612725143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6112149861902447075150095 9168224792853670612725143)
        ·
          refine ⟨13752337189280505919087715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9168224792853670612725143 13752337189280505919087715)
          ·
            refine ⟨20628505783920758878631573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13752337189280505919087715 20628505783920758878631573)
            ·
              refine ⟨966961208621285572435855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20628505783920758878631573 966961208621285572435855)
              ·
                refine ⟨1450441812931928358653783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966961208621285572435855 1450441812931928358653783)
                ·
                  refine ⟨2175662719397892537980675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450441812931928358653783 2175662719397892537980675)
                  ·
                    refine ⟨3263494079096838806971013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2175662719397892537980675 3263494079096838806971013)
                    ·
                      refine ⟨611905139830657276307065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3263494079096838806971013 611905139830657276307065)
                      ·
                        rfl

theorem cell23_1191681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_1191681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191681 prefixEnd_1191681 := by exact prefixLift 1191681
  have htrace : WordTrace (prefixWord ++ tailWord_1191681) baseStart_1191681 baseEnd_1191681 := by
    simpa [prefixWord, tailWord_1191681, baseEnd_1191681] using wordTrace_append hprefix tailTrace_1191681
  have hstable : (prefixWord ++ tailWord_1191681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191681).length < 2 ^ (prefixWord ++ tailWord_1191681).sum := by decide
  have hdescent : baseEnd_1191681 < baseStart_1191681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191732 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1191732 : Nat := 118140960795 + 1191732 * 2 ^ 59
def prefixEnd_1191732 : Nat := 4983230072969 + 3 ^ 40 * 1191732 * 2
def baseEnd_1191732 : Nat := 611931327344036576769331

theorem tailTrace_1191732 : CollatzResearch.WordTrace tailWord_1191732 prefixEnd_1191732 611931327344036576769331 := by
  unfold tailWord_1191732
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733018459282985233364725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28977357945710646977819633 21733018459282985233364725)
  ·
    refine ⟨2037470480557779865627943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21733018459282985233364725 2037470480557779865627943)
    ·
      refine ⟨3056205720836669798441915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037470480557779865627943 3056205720836669798441915)
      ·
        refine ⟨4584308581255004697662873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056205720836669798441915 4584308581255004697662873)
        ·
          refine ⟨3438231435941253523247155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4584308581255004697662873 3438231435941253523247155)
          ·
            refine ⟨5157347153911880284870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438231435941253523247155 5157347153911880284870733)
            ·
              refine ⟨1934005182716955106826525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5157347153911880284870733 1934005182716955106826525)
              ·
                refine ⟨725251943518858165059947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934005182716955106826525 725251943518858165059947)
                ·
                  refine ⟨1087877915278287247589921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725251943518858165059947 1087877915278287247589921)
                  ·
                    refine ⟨815908436458715435692441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1087877915278287247589921 815908436458715435692441)
                    ·
                      refine ⟨611931327344036576769331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 815908436458715435692441 611931327344036576769331)
                      ·
                        rfl

theorem cell23_1191732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1191732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191732 prefixEnd_1191732 := by exact prefixLift 1191732
  have htrace : WordTrace (prefixWord ++ tailWord_1191732) baseStart_1191732 baseEnd_1191732 := by
    simpa [prefixWord, tailWord_1191732, baseEnd_1191732] using wordTrace_append hprefix tailTrace_1191732
  have hstable : (prefixWord ++ tailWord_1191732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191732).length < 2 ^ (prefixWord ++ tailWord_1191732).sum := by decide
  have hdescent : baseEnd_1191732 < baseStart_1191732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191765 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1191765 : Nat := 118140960795 + 1191765 * 2 ^ 59
def prefixEnd_1191765 : Nat := 4983230072969 + 3 ^ 40 * 1191765 * 2
def baseEnd_1191765 : Nat := 611948272205634947656679

theorem tailTrace_1191765 : CollatzResearch.WordTrace tailWord_1191765 prefixEnd_1191765 611948272205634947656679 := by
  unfold tailWord_1191765
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467240527446417102680749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28978160351630944735120499 43467240527446417102680749)
  ·
    refine ⟨16300215197792406413505281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43467240527446417102680749 16300215197792406413505281)
    ·
      refine ⟨12225161398344304810128961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16300215197792406413505281 12225161398344304810128961)
      ·
        refine ⟨9168871048758228607596721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12225161398344304810128961 9168871048758228607596721)
        ·
          refine ⟨6876653286568671455697541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9168871048758228607596721 6876653286568671455697541)
          ·
            refine ⟨1289372491231625897943289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6876653286568671455697541 1289372491231625897943289)
            ·
              refine ⟨967029368423719423457467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289372491231625897943289 967029368423719423457467)
              ·
                refine ⟨1450544052635579135186201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967029368423719423457467 1450544052635579135186201)
                ·
                  refine ⟨1087908039476684351389651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1450544052635579135186201 1087908039476684351389651)
                  ·
                    refine ⟨1631862059215026527084477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1087908039476684351389651 1631862059215026527084477)
                    ·
                      refine ⟨611948272205634947656679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1631862059215026527084477 611948272205634947656679)
                      ·
                        rfl

theorem cell23_1191765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1191765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191765 prefixEnd_1191765 := by exact prefixLift 1191765
  have htrace : WordTrace (prefixWord ++ tailWord_1191765) baseStart_1191765 baseEnd_1191765 := by
    simpa [prefixWord, tailWord_1191765, baseEnd_1191765] using wordTrace_append hprefix tailTrace_1191765
  have hstable : (prefixWord ++ tailWord_1191765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191765).length < 2 ^ (prefixWord ++ tailWord_1191765).sum := by decide
  have hdescent : baseEnd_1191765 < baseStart_1191765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191777 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 9]
def baseStart_1191777 : Nat := 118140960795 + 1191777 * 2 ^ 59
def prefixEnd_1191777 : Nat := 4983230072969 + 3 ^ 40 * 1191777 * 2
def baseEnd_1191777 : Nat := 67994937108165433411847

theorem tailTrace_1191777 : CollatzResearch.WordTrace tailWord_1191777 prefixEnd_1191777 67994937108165433411847 := by
  unfold tailWord_1191777
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467678203402943152117585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28978452135601962101411723 43467678203402943152117585)
  ·
    refine ⟨32600758652552207364088189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43467678203402943152117585 32600758652552207364088189)
    ·
      refine ⟨12225284494707077761533071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32600758652552207364088189 12225284494707077761533071)
      ·
        refine ⟨18337926742060616642299607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12225284494707077761533071 18337926742060616642299607)
        ·
          refine ⟨27506890113090924963449411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18337926742060616642299607 27506890113090924963449411)
          ·
            refine ⟨41260335169636387445174117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27506890113090924963449411 41260335169636387445174117)
            ·
              refine ⟨7736312844306822645970147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41260335169636387445174117 7736312844306822645970147)
              ·
                refine ⟨11604469266460233968955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7736312844306822645970147 11604469266460233968955221)
                ·
                  refine ⟨67994937108165433411847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11604469266460233968955221 67994937108165433411847)
                  ·
                    rfl

theorem cell23_1191777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_1191777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191777 prefixEnd_1191777 := by exact prefixLift 1191777
  have htrace : WordTrace (prefixWord ++ tailWord_1191777) baseStart_1191777 baseEnd_1191777 := by
    simpa [prefixWord, tailWord_1191777, baseEnd_1191777] using wordTrace_append hprefix tailTrace_1191777
  have hstable : (prefixWord ++ tailWord_1191777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191777).length < 2 ^ (prefixWord ++ tailWord_1191777).sum := by decide
  have hdescent : baseEnd_1191777 < baseStart_1191777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191807 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 7]
def baseStart_1191807 : Nat := 118140960795 + 1191807 * 2 ^ 59
def prefixEnd_1191807 : Nat := 4983230072969 + 3 ^ 40 * 1191807 * 2
def baseEnd_1191807 : Nat := 203989946131041261110495

theorem tailTrace_1191807 : CollatzResearch.WordTrace tailWord_1191807 prefixEnd_1191807 203989946131041261110495 := by
  unfold tailWord_1191807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43468772393294258275709675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28979181595529505517139783 43468772393294258275709675)
  ·
    refine ⟨65203158589941387413564513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43468772393294258275709675 65203158589941387413564513)
    ·
      refine ⟨48902368942456040560173385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65203158589941387413564513 48902368942456040560173385)
      ·
        refine ⟨36676776706842030420130039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48902368942456040560173385 36676776706842030420130039)
        ·
          refine ⟨55015165060263045630195059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36676776706842030420130039 55015165060263045630195059)
          ·
            refine ⟨82522747590394568445292589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55015165060263045630195059 82522747590394568445292589)
            ·
              refine ⟨30946030346397963166984721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82522747590394568445292589 30946030346397963166984721)
              ·
                refine ⟨23209522759798472375238541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30946030346397963166984721 23209522759798472375238541)
                ·
                  refine ⟨8703571034924427140714453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23209522759798472375238541 8703571034924427140714453)
                  ·
                    refine ⟨203989946131041261110495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8703571034924427140714453 203989946131041261110495)
                    ·
                      rfl

theorem cell23_1191807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_1191807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191807 prefixEnd_1191807 := by exact prefixLift 1191807
  have htrace : WordTrace (prefixWord ++ tailWord_1191807) baseStart_1191807 baseEnd_1191807 := by
    simpa [prefixWord, tailWord_1191807, baseEnd_1191807] using wordTrace_append hprefix tailTrace_1191807
  have hstable : (prefixWord ++ tailWord_1191807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191807).length < 2 ^ (prefixWord ++ tailWord_1191807).sum := by decide
  have hdescent : baseEnd_1191807 < baseStart_1191807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191811 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 5]
def baseStart_1191811 : Nat := 118140960795 + 1191811 * 2 ^ 59
def prefixEnd_1191811 : Nat := 4983230072969 + 3 ^ 40 * 1191811 * 2
def baseEnd_1191811 : Nat := 67996876923971307520163

theorem tailTrace_1191811 : CollatzResearch.WordTrace tailWord_1191811 prefixEnd_1191811 67996876923971307520163 := by
  unfold tailWord_1191811
  simp only [CollatzResearch.WordTrace]
  refine ⟨43468918285279766958855287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28979278856853177972570191 43468918285279766958855287)
  ·
    refine ⟨65203377427919650438282931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43468918285279766958855287 65203377427919650438282931)
    ·
      refine ⟨97805066141879475657424397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65203377427919650438282931 97805066141879475657424397)
      ·
        refine ⟨36676899803204803371534149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97805066141879475657424397 36676899803204803371534149)
        ·
          refine ⟨6876918713100900632162653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36676899803204803371534149 6876918713100900632162653)
          ·
            refine ⟨2578844517412837737060995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6876918713100900632162653 2578844517412837737060995)
            ·
              refine ⟨3868266776119256605591493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578844517412837737060995 3868266776119256605591493)
              ·
                refine ⟨725300020522360613548405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3868266776119256605591493 725300020522360613548405)
                ·
                  refine ⟨67996876923971307520163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 725300020522360613548405 67996876923971307520163)
                  ·
                    rfl

theorem cell23_1191811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 5].length) (baseStart_1191811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191811 prefixEnd_1191811 := by exact prefixLift 1191811
  have htrace : WordTrace (prefixWord ++ tailWord_1191811) baseStart_1191811 baseEnd_1191811 := by
    simpa [prefixWord, tailWord_1191811, baseEnd_1191811] using wordTrace_append hprefix tailTrace_1191811
  have hstable : (prefixWord ++ tailWord_1191811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191811).length < 2 ^ (prefixWord ++ tailWord_1191811).sum := by decide
  have hdescent : baseEnd_1191811 < baseStart_1191811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191841 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1191841 : Nat := 118140960795 + 1191841 * 2 ^ 59
def prefixEnd_1191841 : Nat := 4983230072969 + 3 ^ 40 * 1191841 * 2
def baseEnd_1191841 : Nat := 203995765578458883435443

theorem tailTrace_1191841 : CollatzResearch.WordTrace tailWord_1191841 prefixEnd_1191841 203995765578458883435443 := by
  unfold tailWord_1191841
  simp only [CollatzResearch.WordTrace]
  refine ⟨43470012475171082082447377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28980008316780721388298251 43470012475171082082447377)
  ·
    refine ⟨32602509356378311561835533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43470012475171082082447377 32602509356378311561835533)
    ·
      refine ⟨12225941008641866835688325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32602509356378311561835533 12225941008641866835688325)
      ·
        refine ⟨2292363939120350031691561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12225941008641866835688325 2292363939120350031691561)
        ·
          refine ⟨1719272954340262523768671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292363939120350031691561 1719272954340262523768671)
          ·
            refine ⟨2578909431510393785653007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719272954340262523768671 2578909431510393785653007)
            ·
              refine ⟨3868364147265590678479511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578909431510393785653007 3868364147265590678479511)
              ·
                refine ⟨5802546220898386017719267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868364147265590678479511 5802546220898386017719267)
                ·
                  refine ⟨8703819331347579026578901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5802546220898386017719267 8703819331347579026578901)
                  ·
                    refine ⟨203995765578458883435443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8703819331347579026578901 203995765578458883435443)
                    ·
                      rfl

theorem cell23_1191841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1191841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191841 prefixEnd_1191841 := by exact prefixLift 1191841
  have htrace : WordTrace (prefixWord ++ tailWord_1191841) baseStart_1191841 baseEnd_1191841 := by
    simpa [prefixWord, tailWord_1191841, baseEnd_1191841] using wordTrace_append hprefix tailTrace_1191841
  have hstable : (prefixWord ++ tailWord_1191841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191841).length < 2 ^ (prefixWord ++ tailWord_1191841).sum := by decide
  have hdescent : baseEnd_1191841 < baseStart_1191841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191871 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 3, 4]
def baseStart_1191871 : Nat := 118140960795 + 1191871 * 2 ^ 59
def prefixEnd_1191871 : Nat := 4983230072969 + 3 ^ 40 * 1191871 * 2
def baseEnd_1191871 : Nat := 204000900385003844310397

theorem tailTrace_1191871 : CollatzResearch.WordTrace tailWord_1191871 prefixEnd_1191871 204000900385003844310397 := by
  unfold tailWord_1191871
  simp only [CollatzResearch.WordTrace]
  refine ⟨43471106665062397206039467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28980737776708264804026311 43471106665062397206039467)
  ·
    refine ⟨65206659997593595809059201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43471106665062397206039467 65206659997593595809059201)
    ·
      refine ⟨48904994998195196856794401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65206659997593595809059201 48904994998195196856794401)
      ·
        refine ⟨36678746248646397642595801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48904994998195196856794401 36678746248646397642595801)
        ·
          refine ⟨27509059686484798231946851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36678746248646397642595801 27509059686484798231946851)
          ·
            refine ⟨41263589529727197347920277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27509059686484798231946851 41263589529727197347920277)
            ·
              refine ⟨1934230759205962375683763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41263589529727197347920277 1934230759205962375683763)
              ·
                refine ⟨2901346138808943563525645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934230759205962375683763 2901346138808943563525645)
                ·
                  refine ⟨1088004802053353836322117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2901346138808943563525645 1088004802053353836322117)
                  ·
                    refine ⟨204000900385003844310397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088004802053353836322117 204000900385003844310397)
                    ·
                      rfl

theorem cell23_1191871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_1191871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191871 prefixEnd_1191871 := by exact prefixLift 1191871
  have htrace : WordTrace (prefixWord ++ tailWord_1191871) baseStart_1191871 baseEnd_1191871 := by
    simpa [prefixWord, tailWord_1191871, baseEnd_1191871] using wordTrace_append hprefix tailTrace_1191871
  have hstable : (prefixWord ++ tailWord_1191871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191871).length < 2 ^ (prefixWord ++ tailWord_1191871).sum := by decide
  have hdescent : baseEnd_1191871 < baseStart_1191871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191928 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_1191928 : Nat := 118140960795 + 1191928 * 2 ^ 59
def prefixEnd_1191928 : Nat := 4983230072969 + 3 ^ 40 * 1191928 * 2
def baseEnd_1191928 : Nat := 612031969552317809918429

theorem tailTrace_1191928 : CollatzResearch.WordTrace tailWord_1191928 prefixEnd_1191928 612031969552317809918429 := by
  unfold tailWord_1191928
  simp only [CollatzResearch.WordTrace]
  refine ⟨21736592812927947970432219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28982123750570597293909625 21736592812927947970432219)
  ·
    refine ⟨32604889219391921955648329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21736592812927947970432219 32604889219391921955648329)
    ·
      refine ⟨24453666914543941466736247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32604889219391921955648329 24453666914543941466736247)
      ·
        refine ⟨36680500371815912200104371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24453666914543941466736247 36680500371815912200104371)
        ·
          refine ⟨55020750557723868300156557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36680500371815912200104371 55020750557723868300156557)
          ·
            refine ⟨20632781459146450612558709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55020750557723868300156557 20632781459146450612558709)
            ·
              refine ⟨1934323261794979744927379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20632781459146450612558709 1934323261794979744927379)
              ·
                refine ⟨2901484892692469617391069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934323261794979744927379 2901484892692469617391069)
                ·
                  refine ⟨1088056834759676106521651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2901484892692469617391069 1088056834759676106521651)
                  ·
                    refine ⟨1632085252139514159782477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088056834759676106521651 1632085252139514159782477)
                    ·
                      refine ⟨612031969552317809918429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632085252139514159782477 612031969552317809918429)
                      ·
                        rfl

theorem cell23_1191928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_1191928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191928 prefixEnd_1191928 := by exact prefixLift 1191928
  have htrace : WordTrace (prefixWord ++ tailWord_1191928) baseStart_1191928 baseEnd_1191928 := by
    simpa [prefixWord, tailWord_1191928, baseEnd_1191928] using wordTrace_append hprefix tailTrace_1191928
  have hstable : (prefixWord ++ tailWord_1191928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191928).length < 2 ^ (prefixWord ++ tailWord_1191928).sum := by decide
  have hdescent : baseEnd_1191928 < baseStart_1191928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191949 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1191949 : Nat := 118140960795 + 1191949 * 2 ^ 59
def prefixEnd_1191949 : Nat := 4983230072969 + 3 ^ 40 * 1191949 * 2
def baseEnd_1191949 : Nat := 612042752646062227755833

theorem tailTrace_1191949 : CollatzResearch.WordTrace tailWord_1191949 prefixEnd_1191949 612042752646062227755833 := by
  unfold tailWord_1191949
  simp only [CollatzResearch.WordTrace]
  refine ⟨43473951558779816527378901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28982634372519877684919267 43473951558779816527378901)
  ·
    refine ⟨1018920739658901949860443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43473951558779816527378901 1018920739658901949860443)
    ·
      refine ⟨1528381109488352924790665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018920739658901949860443 1528381109488352924790665)
      ·
        refine ⟨1146285832116264693592999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528381109488352924790665 1146285832116264693592999)
        ·
          refine ⟨1719428748174397040389499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146285832116264693592999 1719428748174397040389499)
          ·
            refine ⟨2579143122261595560584249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719428748174397040389499 2579143122261595560584249)
            ·
              refine ⟨1934357341696196670438187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579143122261595560584249 1934357341696196670438187)
              ·
                refine ⟨2901536012544295005657281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934357341696196670438187 2901536012544295005657281)
                ·
                  refine ⟨2176152009408221254242961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901536012544295005657281 2176152009408221254242961)
                  ·
                    refine ⟨1632114007056165940682221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2176152009408221254242961 1632114007056165940682221)
                    ·
                      refine ⟨612042752646062227755833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632114007056165940682221 612042752646062227755833)
                      ·
                        rfl

theorem cell23_1191949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1191949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191949 prefixEnd_1191949 := by exact prefixLift 1191949
  have htrace : WordTrace (prefixWord ++ tailWord_1191949) baseStart_1191949 baseEnd_1191949 := by
    simpa [prefixWord, tailWord_1191949, baseEnd_1191949] using wordTrace_append hprefix tailTrace_1191949
  have hstable : (prefixWord ++ tailWord_1191949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191949).length < 2 ^ (prefixWord ++ tailWord_1191949).sum := by decide
  have hdescent : baseEnd_1191949 < baseStart_1191949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191965 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1191965 : Nat := 118140960795 + 1191965 * 2 ^ 59
def prefixEnd_1191965 : Nat := 4983230072969 + 3 ^ 40 * 1191965 * 2
def baseEnd_1191965 : Nat := 204016989445511388385253

theorem tailTrace_1191965 : CollatzResearch.WordTrace tailWord_1191965 prefixEnd_1191965 204016989445511388385253 := by
  unfold tailWord_1191965
  simp only [CollatzResearch.WordTrace]
  refine ⟨43474535126721851259961349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28983023417814567506640899 43474535126721851259961349)
  ·
    refine ⟨8151475336260347111242753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43474535126721851259961349 8151475336260347111242753)
    ·
      refine ⟨6113606502195260333432065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8151475336260347111242753 6113606502195260333432065)
      ·
        refine ⟨4585204876646445250074049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6113606502195260333432065 4585204876646445250074049)
        ·
          refine ⟨3438903657484833937555537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585204876646445250074049 3438903657484833937555537)
          ·
            refine ⟨2579177743113625453166653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3438903657484833937555537 2579177743113625453166653)
            ·
              refine ⟨967191653667609544937495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2579177743113625453166653 967191653667609544937495)
              ·
                refine ⟨1450787480501414317406243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967191653667609544937495 1450787480501414317406243)
                ·
                  refine ⟨2176181220752121476109365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450787480501414317406243 2176181220752121476109365)
                  ·
                    refine ⟨204016989445511388385253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2176181220752121476109365 204016989445511388385253)
                    ·
                      rfl

theorem cell23_1191965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1191965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1191965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1191965 prefixEnd_1191965 := by exact prefixLift 1191965
  have htrace : WordTrace (prefixWord ++ tailWord_1191965) baseStart_1191965 baseEnd_1191965 := by
    simpa [prefixWord, tailWord_1191965, baseEnd_1191965] using wordTrace_append hprefix tailTrace_1191965
  have hstable : (prefixWord ++ tailWord_1191965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191965).length < 2 ^ (prefixWord ++ tailWord_1191965).sum := by decide
  have hdescent : baseEnd_1191965 < baseStart_1191965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192035 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1192035 : Nat := 118140960795 + 1192035 * 2 ^ 59
def prefixEnd_1192035 : Nat := 4983230072969 + 3 ^ 40 * 1192035 * 2
def baseEnd_1192035 : Nat := 612086911982348891280437

theorem tailTrace_1192035 : CollatzResearch.WordTrace tailWord_1192035 prefixEnd_1192035 612086911982348891280437 := by
  unfold tailWord_1192035
  simp only [CollatzResearch.WordTrace]
  refine ⟨43477088236468253215009559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28984725490978835476673039 43477088236468253215009559)
  ·
    refine ⟨65215632354702379822514339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43477088236468253215009559 65215632354702379822514339)
    ·
      refine ⟨97823448532053569733771509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65215632354702379822514339 97823448532053569733771509)
      ·
        refine ⟨9170948299880022162541079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97823448532053569733771509 9170948299880022162541079)
        ·
          refine ⟨13756422449820033243811619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9170948299880022162541079 13756422449820033243811619)
          ·
            refine ⟨20634633674730049865717429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756422449820033243811619 20634633674730049865717429)
            ·
              refine ⟨1934496907005942174911009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20634633674730049865717429 1934496907005942174911009)
              ·
                refine ⟨1450872680254456631183257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1934496907005942174911009 1450872680254456631183257)
                ·
                  refine ⟨1088154510190842473387443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1450872680254456631183257 1088154510190842473387443)
                  ·
                    refine ⟨1632231765286263710081165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088154510190842473387443 1632231765286263710081165)
                    ·
                      refine ⟨612086911982348891280437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632231765286263710081165 612086911982348891280437)
                      ·
                        rfl

theorem cell23_1192035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1192035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192035 prefixEnd_1192035 := by exact prefixLift 1192035
  have htrace : WordTrace (prefixWord ++ tailWord_1192035) baseStart_1192035 baseEnd_1192035 := by
    simpa [prefixWord, tailWord_1192035, baseEnd_1192035] using wordTrace_append hprefix tailTrace_1192035
  have hstable : (prefixWord ++ tailWord_1192035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192035).length < 2 ^ (prefixWord ++ tailWord_1192035).sum := by decide
  have hdescent : baseEnd_1192035 < baseStart_1192035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192071 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1192071 : Nat := 118140960795 + 1192071 * 2 ^ 59
def prefixEnd_1192071 : Nat := 4983230072969 + 3 ^ 40 * 1192071 * 2
def baseEnd_1192071 : Nat := 612105397285910750430271

theorem tailTrace_1192071 : CollatzResearch.WordTrace tailWord_1192071 prefixEnd_1192071 612105397285910750430271 := by
  unfold tailWord_1192071
  simp only [CollatzResearch.WordTrace]
  refine ⟨43478401264337831363320067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28985600842891887575546711 43478401264337831363320067)
  ·
    refine ⟨65217601896506747044980101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43478401264337831363320067 65217601896506747044980101)
    ·
      refine ⟨12228300355595015070933769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65217601896506747044980101 12228300355595015070933769)
      ·
        refine ⟨9171225266696261303200327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12228300355595015070933769 9171225266696261303200327)
        ·
          refine ⟨13756837900044391954800491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171225266696261303200327 13756837900044391954800491)
          ·
            refine ⟨20635256850066587932200737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756837900044391954800491 20635256850066587932200737)
            ·
              refine ⟨15476442637549940949150553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20635256850066587932200737 15476442637549940949150553)
              ·
                refine ⟨11607331978162455711862915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15476442637549940949150553 11607331978162455711862915)
                ·
                  refine ⟨17410997967243683567794373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11607331978162455711862915 17410997967243683567794373)
                  ·
                    refine ⟨3264562118858190668961445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17410997967243683567794373 3264562118858190668961445)
                    ·
                      refine ⟨612105397285910750430271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3264562118858190668961445 612105397285910750430271)
                      ·
                        rfl

theorem cell23_1192071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1192071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192071 prefixEnd_1192071 := by exact prefixLift 1192071
  have htrace : WordTrace (prefixWord ++ tailWord_1192071) baseStart_1192071 baseEnd_1192071 := by
    simpa [prefixWord, tailWord_1192071, baseEnd_1192071] using wordTrace_append hprefix tailTrace_1192071
  have hstable : (prefixWord ++ tailWord_1192071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192071).length < 2 ^ (prefixWord ++ tailWord_1192071).sum := by decide
  have hdescent : baseEnd_1192071 < baseStart_1192071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192091 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3]
def baseStart_1192091 : Nat := 118140960795 + 1192091 * 2 ^ 59
def prefixEnd_1192091 : Nat := 4983230072969 + 3 ^ 40 * 1192091 * 2
def baseEnd_1192091 : Nat := 612115666899000672180179

theorem tailTrace_1192091 : CollatzResearch.WordTrace tailWord_1192091 prefixEnd_1192091 612115666899000672180179 := by
  unfold tailWord_1192091
  simp only [CollatzResearch.WordTrace]
  refine ⟨43479130724265374779048127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28986087149510249852698751 43479130724265374779048127)
  ·
    refine ⟨65218696086398062168572191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43479130724265374779048127 65218696086398062168572191)
    ·
      refine ⟨97828044129597093252858287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65218696086398062168572191 97828044129597093252858287)
      ·
        refine ⟨146742066194395639879287431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97828044129597093252858287 146742066194395639879287431)
        ·
          refine ⟨220113099291593459818931147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146742066194395639879287431 220113099291593459818931147)
          ·
            refine ⟨330169648937390189728396721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220113099291593459818931147 330169648937390189728396721)
            ·
              refine ⟨247627236703042642296297541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330169648937390189728396721 247627236703042642296297541)
              ·
                refine ⟨46430106881820495430555789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247627236703042642296297541 46430106881820495430555789)
                ·
                  refine ⟨17411290080682685786458421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46430106881820495430555789 17411290080682685786458421)
                  ·
                    refine ⟨1632308445064001792480477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17411290080682685786458421 1632308445064001792480477)
                    ·
                      refine ⟨612115666899000672180179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632308445064001792480477 612115666899000672180179)
                      ·
                        rfl

theorem cell23_1192091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3].length) (baseStart_1192091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192091 prefixEnd_1192091 := by exact prefixLift 1192091
  have htrace : WordTrace (prefixWord ++ tailWord_1192091) baseStart_1192091 baseEnd_1192091 := by
    simpa [prefixWord, tailWord_1192091, baseEnd_1192091] using wordTrace_append hprefix tailTrace_1192091
  have hstable : (prefixWord ++ tailWord_1192091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192091).length < 2 ^ (prefixWord ++ tailWord_1192091).sum := by decide
  have hdescent : baseEnd_1192091 < baseStart_1192091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192092 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1192092 : Nat := 118140960795 + 1192092 * 2 ^ 59
def prefixEnd_1192092 : Nat := 4983230072969 + 3 ^ 40 * 1192092 * 2
def baseEnd_1192092 : Nat := 612116180379655168267675

theorem tailTrace_1192092 : CollatzResearch.WordTrace tailWord_1192092 prefixEnd_1192092 612116180379655168267675 := by
  unfold tailWord_1192092
  simp only [CollatzResearch.WordTrace]
  refine ⟨21739583598630875974917265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28986111464841167966556353 21739583598630875974917265)
  ·
    refine ⟨16304687698973156981187949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21739583598630875974917265 16304687698973156981187949)
    ·
      refine ⟨6114257887114933867945481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16304687698973156981187949 6114257887114933867945481)
      ·
        refine ⟨4585693415336200400959111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6114257887114933867945481 4585693415336200400959111)
        ·
          refine ⟨6878540123004300601438667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585693415336200400959111 6878540123004300601438667)
          ·
            refine ⟨10317810184506450902158001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878540123004300601438667 10317810184506450902158001)
            ·
              refine ⟨7738357638379838176618501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10317810184506450902158001 7738357638379838176618501)
              ·
                refine ⟨1450942057196219658115969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7738357638379838176618501 1450942057196219658115969)
                ·
                  refine ⟨1088206542897164743586977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1450942057196219658115969 1088206542897164743586977)
                  ·
                    refine ⟨816154907172873557690233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088206542897164743586977 816154907172873557690233)
                    ·
                      refine ⟨612116180379655168267675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816154907172873557690233 612116180379655168267675)
                      ·
                        rfl

theorem cell23_1192092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1192092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192092 prefixEnd_1192092 := by exact prefixLift 1192092
  have htrace : WordTrace (prefixWord ++ tailWord_1192092) baseStart_1192092 baseEnd_1192092 := by
    simpa [prefixWord, tailWord_1192092, baseEnd_1192092] using wordTrace_append hprefix tailTrace_1192092
  have hstable : (prefixWord ++ tailWord_1192092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192092).length < 2 ^ (prefixWord ++ tailWord_1192092).sum := by decide
  have hdescent : baseEnd_1192092 < baseStart_1192092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192109 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1192109 : Nat := 118140960795 + 1192109 * 2 ^ 59
def prefixEnd_1192109 : Nat := 4983230072969 + 3 ^ 40 * 1192109 * 2
def baseEnd_1192109 : Nat := 612124909550781601755097

theorem tailTrace_1192109 : CollatzResearch.WordTrace tailWord_1192109 prefixEnd_1192109 612124909550781601755097 := by
  unfold tailWord_1192109
  simp only [CollatzResearch.WordTrace]
  refine ⟨43479787238200163853203381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28986524825466775902135587 43479787238200163853203381)
  ·
    refine ⟨4076230053581265361237817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43479787238200163853203381 4076230053581265361237817)
    ·
      refine ⟨3057172540185949020928363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4076230053581265361237817 3057172540185949020928363)
      ·
        refine ⟨4585758810278923531392545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057172540185949020928363 4585758810278923531392545)
        ·
          refine ⟨3439319107709192648544409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585758810278923531392545 3439319107709192648544409)
          ·
            refine ⟨2579489330781894486408307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439319107709192648544409 2579489330781894486408307)
            ·
              refine ⟨3869233996172841729612461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579489330781894486408307 3869233996172841729612461)
              ·
                refine ⟨1450962748564815648604673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3869233996172841729612461 1450962748564815648604673)
                ·
                  refine ⟨1088222061423611736453505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1450962748564815648604673 1088222061423611736453505)
                  ·
                    refine ⟨816166546067708802340129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088222061423611736453505 816166546067708802340129)
                    ·
                      refine ⟨612124909550781601755097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816166546067708802340129 612124909550781601755097)
                      ·
                        rfl

theorem cell23_1192109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1192109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192109 prefixEnd_1192109 := by exact prefixLift 1192109
  have htrace : WordTrace (prefixWord ++ tailWord_1192109) baseStart_1192109 baseEnd_1192109 := by
    simpa [prefixWord, tailWord_1192109, baseEnd_1192109] using wordTrace_append hprefix tailTrace_1192109
  have hstable : (prefixWord ++ tailWord_1192109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192109).length < 2 ^ (prefixWord ++ tailWord_1192109).sum := by decide
  have hdescent : baseEnd_1192109 < baseStart_1192109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192111 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 6, 5]
def baseStart_1192111 : Nat := 118140960795 + 1192111 * 2 ^ 59
def prefixEnd_1192111 : Nat := 4983230072969 + 3 ^ 40 * 1192111 * 2
def baseEnd_1192111 : Nat := 204041978837363531310029

theorem tailTrace_1192111 : CollatzResearch.WordTrace tailWord_1192111 prefixEnd_1192111 204041978837363531310029 := by
  unfold tailWord_1192111
  simp only [CollatzResearch.WordTrace]
  refine ⟨43479860184192918194776187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28986573456128612129850791 43479860184192918194776187)
  ·
    refine ⟨65219790276289377292164281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43479860184192918194776187 65219790276289377292164281)
    ·
      refine ⟨48914842707217032969123211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65219790276289377292164281 48914842707217032969123211)
      ·
        refine ⟨73372264060825549453684817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48914842707217032969123211 73372264060825549453684817)
        ·
          refine ⟨55029198045619162090263613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73372264060825549453684817 55029198045619162090263613)
          ·
            refine ⟨20635949267107185783848855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55029198045619162090263613 20635949267107185783848855)
            ·
              refine ⟨30953923900660778675773283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20635949267107185783848855 30953923900660778675773283)
              ·
                refine ⟨46430885850991168013659925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30953923900660778675773283 46430885850991168013659925)
                ·
                  refine ⟨2176447774265211000640309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46430885850991168013659925 2176447774265211000640309)
                  ·
                    refine ⟨204041978837363531310029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2176447774265211000640309 204041978837363531310029)
                    ·
                      rfl

theorem cell23_1192111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_1192111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192111 prefixEnd_1192111 := by exact prefixLift 1192111
  have htrace : WordTrace (prefixWord ++ tailWord_1192111) baseStart_1192111 baseEnd_1192111 := by
    simpa [prefixWord, tailWord_1192111, baseEnd_1192111] using wordTrace_append hprefix tailTrace_1192111
  have hstable : (prefixWord ++ tailWord_1192111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192111).length < 2 ^ (prefixWord ++ tailWord_1192111).sum := by decide
  have hdescent : baseEnd_1192111 < baseStart_1192111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192121 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1192121 : Nat := 118140960795 + 1192121 * 2 ^ 59
def prefixEnd_1192121 : Nat := 4983230072969 + 3 ^ 40 * 1192121 * 2
def baseEnd_1192121 : Nat := 612131071318635554805041

theorem tailTrace_1192121 : CollatzResearch.WordTrace tailWord_1192121 prefixEnd_1192121 612131071318635554805041 := by
  unfold tailWord_1192121
  simp only [CollatzResearch.WordTrace]
  refine ⟨43480224914156689902640217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28986816609437793268426811 43480224914156689902640217)
  ·
    refine ⟨32610168685617517426980163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43480224914156689902640217 32610168685617517426980163)
    ·
      refine ⟨48915253028426276140470245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32610168685617517426980163 48915253028426276140470245)
      ·
        refine ⟨9171609942829926776338171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48915253028426276140470245 9171609942829926776338171)
        ·
          refine ⟨13757414914244890164507257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171609942829926776338171 13757414914244890164507257)
          ·
            refine ⟨10318061185683667623380443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13757414914244890164507257 10318061185683667623380443)
            ·
              refine ⟨15477091778525501435070665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10318061185683667623380443 15477091778525501435070665)
              ·
                refine ⟨11607818833894126076302999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15477091778525501435070665 11607818833894126076302999)
                ·
                  refine ⟨17411728250841189114454499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11607818833894126076302999 17411728250841189114454499)
                  ·
                    refine ⟨26117592376261783671681749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17411728250841189114454499 26117592376261783671681749)
                    ·
                      refine ⟨612131071318635554805041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26117592376261783671681749 612131071318635554805041)
                      ·
                        rfl

theorem cell23_1192121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1192121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192121 prefixEnd_1192121 := by exact prefixLift 1192121
  have htrace : WordTrace (prefixWord ++ tailWord_1192121) baseStart_1192121 baseEnd_1192121 := by
    simpa [prefixWord, tailWord_1192121, baseEnd_1192121] using wordTrace_append hprefix tailTrace_1192121
  have hstable : (prefixWord ++ tailWord_1192121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192121).length < 2 ^ (prefixWord ++ tailWord_1192121).sum := by decide
  have hdescent : baseEnd_1192121 < baseStart_1192121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192128 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_1192128 : Nat := 118140960795 + 1192128 * 2 ^ 59
def prefixEnd_1192128 : Nat := 4983230072969 + 3 ^ 40 * 1192128 * 2
def baseEnd_1192128 : Nat := 204044888561072342472503

theorem tailTrace_1192128 : CollatzResearch.WordTrace tailWord_1192128 prefixEnd_1192128 204044888561072342472503 := by
  unfold tailWord_1192128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740240112565665049072519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28986986816754220065430025 21740240112565665049072519)
  ·
    refine ⟨32610360168848497573608779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21740240112565665049072519 32610360168848497573608779)
    ·
      refine ⟨48915540253272746360413169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32610360168848497573608779 48915540253272746360413169)
      ·
        refine ⟨36686655189954559770309877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48915540253272746360413169 36686655189954559770309877)
        ·
          refine ⟨3439373924058239978466551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36686655189954559770309877 3439373924058239978466551)
          ·
            refine ⟨5159060886087359967699827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439373924058239978466551 5159060886087359967699827)
            ·
              refine ⟨7738591329131039951549741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159060886087359967699827 7738591329131039951549741)
              ·
                refine ⟨2901971748424139981831153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7738591329131039951549741 2901971748424139981831153)
                ·
                  refine ⟨2176478811318104986373365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901971748424139981831153 2176478811318104986373365)
                  ·
                    refine ⟨204044888561072342472503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2176478811318104986373365 204044888561072342472503)
                    ·
                      rfl

theorem cell23_1192128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_1192128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192128 prefixEnd_1192128 := by exact prefixLift 1192128
  have htrace : WordTrace (prefixWord ++ tailWord_1192128) baseStart_1192128 baseEnd_1192128 := by
    simpa [prefixWord, tailWord_1192128, baseEnd_1192128] using wordTrace_append hprefix tailTrace_1192128
  have hstable : (prefixWord ++ tailWord_1192128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192128).length < 2 ^ (prefixWord ++ tailWord_1192128).sum := by decide
  have hdescent : baseEnd_1192128 < baseStart_1192128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192131 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1192131 : Nat := 118140960795 + 1192131 * 2 ^ 59
def prefixEnd_1192131 : Nat := 4983230072969 + 3 ^ 40 * 1192131 * 2
def baseEnd_1192131 : Nat := 612136206125180515679995

theorem tailTrace_1192131 : CollatzResearch.WordTrace tailWord_1192131 prefixEnd_1192131 612136206125180515679995 := by
  unfold tailWord_1192131
  simp only [CollatzResearch.WordTrace]
  refine ⟨43480589644120461610504247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987059762746974407002831 43480589644120461610504247)
  ·
    refine ⟨65220884466180692415756371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43480589644120461610504247 65220884466180692415756371)
    ·
      refine ⟨97831326699271038623634557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65220884466180692415756371 97831326699271038623634557)
      ·
        refine ⟨36686747512226639483862959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97831326699271038623634557 36686747512226639483862959)
        ·
          refine ⟨55030121268339959225794439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36686747512226639483862959 55030121268339959225794439)
          ·
            refine ⟨82545181902509938838691659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55030121268339959225794439 82545181902509938838691659)
            ·
              refine ⟨123817772853764908258037489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82545181902509938838691659 123817772853764908258037489)
              ·
                refine ⟨92863329640323681193528117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123817772853764908258037489 92863329640323681193528117)
                ·
                  refine ⟨8705937153780345111893261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92863329640323681193528117 8705937153780345111893261)
                  ·
                    refine ⟨3264726432667629416959973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8705937153780345111893261 3264726432667629416959973)
                    ·
                      refine ⟨612136206125180515679995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3264726432667629416959973 612136206125180515679995)
                      ·
                        rfl

theorem cell23_1192131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1192131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192131 prefixEnd_1192131 := by exact prefixLift 1192131
  have htrace : WordTrace (prefixWord ++ tailWord_1192131) baseStart_1192131 baseEnd_1192131 := by
    simpa [prefixWord, tailWord_1192131, baseEnd_1192131] using wordTrace_append hprefix tailTrace_1192131
  have hstable : (prefixWord ++ tailWord_1192131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192131).length < 2 ^ (prefixWord ++ tailWord_1192131).sum := by decide
  have hdescent : baseEnd_1192131 < baseStart_1192131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192149 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 5]
def baseStart_1192149 : Nat := 118140960795 + 1192149 * 2 ^ 59
def prefixEnd_1192149 : Nat := 4983230072969 + 3 ^ 40 * 1192149 * 2
def baseEnd_1192149 : Nat := 68016160975217938361657

theorem tailTrace_1192149 : CollatzResearch.WordTrace tailWord_1192149 prefixEnd_1192149 68016160975217938361657 := by
  unfold tailWord_1192149
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481246158055250684659501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987497438703500456439667 43481246158055250684659501)
  ·
    refine ⟨16305467309270719006747313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43481246158055250684659501 16305467309270719006747313)
    ·
      refine ⟨12229100481953039255060485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16305467309270719006747313 12229100481953039255060485)
      ·
        refine ⟨2292956340366194860323841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12229100481953039255060485 2292956340366194860323841)
        ·
          refine ⟨1719717255274646145242881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292956340366194860323841 1719717255274646145242881)
          ·
            refine ⟨1289787941455984608932161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1719717255274646145242881 1289787941455984608932161)
            ·
              refine ⟨967340956091988456699121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289787941455984608932161 967340956091988456699121)
              ·
                refine ⟨725505717068991342524341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967340956091988456699121 725505717068991342524341)
                ·
                  refine ⟨68016160975217938361657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 725505717068991342524341 68016160975217938361657)
                  ·
                    rfl

theorem cell23_1192149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_1192149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192149 prefixEnd_1192149 := by exact prefixLift 1192149
  have htrace : WordTrace (prefixWord ++ tailWord_1192149) baseStart_1192149 baseEnd_1192149 := by
    simpa [prefixWord, tailWord_1192149, baseEnd_1192149] using wordTrace_append hprefix tailTrace_1192149
  have hstable : (prefixWord ++ tailWord_1192149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192149).length < 2 ^ (prefixWord ++ tailWord_1192149).sum := by decide
  have hdescent : baseEnd_1192149 < baseStart_1192149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192151 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1192151 : Nat := 118140960795 + 1192151 * 2 ^ 59
def prefixEnd_1192151 : Nat := 4983230072969 + 3 ^ 40 * 1192151 * 2
def baseEnd_1192151 : Nat := 612146475738270437429903

theorem tailTrace_1192151 : CollatzResearch.WordTrace tailWord_1192151 prefixEnd_1192151 612146475738270437429903 := by
  unfold tailWord_1192151
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481319104048005026232307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987546069365336684154871 43481319104048005026232307)
  ·
    refine ⟨65221978656072007539348461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43481319104048005026232307 65221978656072007539348461)
    ·
      refine ⟨24458241996027002827255673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65221978656072007539348461 24458241996027002827255673)
      ·
        refine ⟨18343681497020252120441755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24458241996027002827255673 18343681497020252120441755)
        ·
          refine ⟨27515522245530378180662633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18343681497020252120441755 27515522245530378180662633)
          ·
            refine ⟨20636641684147783635496975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27515522245530378180662633 20636641684147783635496975)
            ·
              refine ⟨30954962526221675453245463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20636641684147783635496975 30954962526221675453245463)
              ·
                refine ⟨46432443789332513179868195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30954962526221675453245463 46432443789332513179868195)
                ·
                  refine ⟨69648665683998769769802293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46432443789332513179868195 69648665683998769769802293)
                  ·
                    refine ⟨6529562407874884665918965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69648665683998769769802293 6529562407874884665918965)
                    ·
                      refine ⟨612146475738270437429903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6529562407874884665918965 612146475738270437429903)
                      ·
                        rfl

theorem cell23_1192151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1192151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192151 prefixEnd_1192151 := by exact prefixLift 1192151
  have htrace : WordTrace (prefixWord ++ tailWord_1192151) baseStart_1192151 baseEnd_1192151 := by
    simpa [prefixWord, tailWord_1192151, baseEnd_1192151] using wordTrace_append hprefix tailTrace_1192151
  have hstable : (prefixWord ++ tailWord_1192151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192151).length < 2 ^ (prefixWord ++ tailWord_1192151).sum := by decide
  have hdescent : baseEnd_1192151 < baseStart_1192151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192165 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1192165 : Nat := 118140960795 + 1192165 * 2 ^ 59
def prefixEnd_1192165 : Nat := 4983230072969 + 3 ^ 40 * 1192165 * 2
def baseEnd_1192165 : Nat := 612153664467433382654839

theorem tailTrace_1192165 : CollatzResearch.WordTrace tailWord_1192165 prefixEnd_1192165 612153664467433382654839 := by
  unfold tailWord_1192165
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481829725997285417241949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987886483998190278161299 43481829725997285417241949)
  ·
    refine ⟨16305686147248982031465731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43481829725997285417241949 16305686147248982031465731)
    ·
      refine ⟨24458529220873473047198597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16305686147248982031465731 24458529220873473047198597)
      ·
        refine ⟨4585974228913776196349737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24458529220873473047198597 4585974228913776196349737)
        ·
          refine ⟨3439480671685332147262303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585974228913776196349737 3439480671685332147262303)
          ·
            refine ⟨5159221007527998220893455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439480671685332147262303 5159221007527998220893455)
            ·
              refine ⟨7738831511291997331340183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159221007527998220893455 7738831511291997331340183)
              ·
                refine ⟨11608247266937995997010275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7738831511291997331340183 11608247266937995997010275)
                ·
                  refine ⟨17412370900406993995515413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11608247266937995997010275 17412370900406993995515413)
                  ·
                    refine ⟨816204885956577843539785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17412370900406993995515413 816204885956577843539785)
                    ·
                      refine ⟨612153664467433382654839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816204885956577843539785 612153664467433382654839)
                      ·
                        rfl

theorem cell23_1192165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1192165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192165 prefixEnd_1192165 := by exact prefixLift 1192165
  have htrace : WordTrace (prefixWord ++ tailWord_1192165) baseStart_1192165 baseEnd_1192165 := by
    simpa [prefixWord, tailWord_1192165, baseEnd_1192165] using wordTrace_append hprefix tailTrace_1192165
  have hstable : (prefixWord ++ tailWord_1192165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192165).length < 2 ^ (prefixWord ++ tailWord_1192165).sum := by decide
  have hdescent : baseEnd_1192165 < baseStart_1192165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192175 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 3, 4]
def baseStart_1192175 : Nat := 118140960795 + 1192175 * 2 ^ 59
def prefixEnd_1192175 : Nat := 4983230072969 + 3 ^ 40 * 1192175 * 2
def baseEnd_1192175 : Nat := 204052933091326114509931

theorem tailTrace_1192175 : CollatzResearch.WordTrace tailWord_1192175 prefixEnd_1192175 204052933091326114509931 := by
  unfold tailWord_1192175
  simp only [CollatzResearch.WordTrace]
  refine ⟨43482194455961057125105979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28988129637307371416737319 43482194455961057125105979)
  ·
    refine ⟨65223291683941585687658969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43482194455961057125105979 65223291683941585687658969)
    ·
      refine ⟨48917468762956189265744227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65223291683941585687658969 48917468762956189265744227)
      ·
        refine ⟨73376203144434283898616341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48917468762956189265744227 73376203144434283898616341)
        ·
          refine ⟨3439509522395357057747641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73376203144434283898616341 3439509522395357057747641)
          ·
            refine ⟨2579632141796517793310731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439509522395357057747641 2579632141796517793310731)
            ·
              refine ⟨3869448212694776689966097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579632141796517793310731 3869448212694776689966097)
              ·
                refine ⟨2902086159521082517474573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3869448212694776689966097 2902086159521082517474573)
                ·
                  refine ⟨1088282309820405944052965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2902086159521082517474573 1088282309820405944052965)
                  ·
                    refine ⟨204052933091326114509931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088282309820405944052965 204052933091326114509931)
                    ·
                      rfl

theorem cell23_1192175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_1192175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192175 prefixEnd_1192175 := by exact prefixLift 1192175
  have htrace : WordTrace (prefixWord ++ tailWord_1192175) baseStart_1192175 baseEnd_1192175 := by
    simpa [prefixWord, tailWord_1192175, baseEnd_1192175] using wordTrace_append hprefix tailTrace_1192175
  have hstable : (prefixWord ++ tailWord_1192175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192175).length < 2 ^ (prefixWord ++ tailWord_1192175).sum := by decide
  have hdescent : baseEnd_1192175 < baseStart_1192175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192225 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1192225 : Nat := 118140960795 + 1192225 * 2 ^ 59
def prefixEnd_1192225 : Nat := 4983230072969 + 3 ^ 40 * 1192225 * 2
def baseEnd_1192225 : Nat := 612184473306703147904563

theorem tailTrace_1192225 : CollatzResearch.WordTrace tailWord_1192225 prefixEnd_1192225 612184473306703147904563 := by
  unfold tailWord_1192225
  simp only [CollatzResearch.WordTrace]
  refine ⟨43484018105779915664426129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28989345403853277109617419 43484018105779915664426129)
  ·
    refine ⟨32613013579334936748319597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43484018105779915664426129 32613013579334936748319597)
    ·
      refine ⟨12229880092250601280619849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32613013579334936748319597 12229880092250601280619849)
      ·
        refine ⟨9172410069187950960464887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12229880092250601280619849 9172410069187950960464887)
        ·
          refine ⟨13758615103781926440697331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172410069187950960464887 13758615103781926440697331)
          ·
            refine ⟨20637922655672889661045997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758615103781926440697331 20637922655672889661045997)
            ·
              refine ⟨7739220995877333622892249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20637922655672889661045997 7739220995877333622892249)
              ·
                refine ⟨5804415746908000217169187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7739220995877333622892249 5804415746908000217169187)
                ·
                  refine ⟨8706623620362000325753781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5804415746908000217169187 8706623620362000325753781)
                  ·
                    refine ⟨816245964408937530539417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8706623620362000325753781 816245964408937530539417)
                    ·
                      refine ⟨612184473306703147904563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816245964408937530539417 612184473306703147904563)
                      ·
                        rfl

theorem cell23_1192225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1192225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192225 prefixEnd_1192225 := by exact prefixLift 1192225
  have htrace : WordTrace (prefixWord ++ tailWord_1192225) baseStart_1192225 baseEnd_1192225 := by
    simpa [prefixWord, tailWord_1192225, baseEnd_1192225] using wordTrace_append hprefix tailTrace_1192225
  have hstable : (prefixWord ++ tailWord_1192225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192225).length < 2 ^ (prefixWord ++ tailWord_1192225).sum := by decide
  have hdescent : baseEnd_1192225 < baseStart_1192225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192248 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_1192248 : Nat := 118140960795 + 1192248 * 2 ^ 59
def prefixEnd_1192248 : Nat := 4983230072969 + 3 ^ 40 * 1192248 * 2
def baseEnd_1192248 : Nat := 204065427787252185972319

theorem tailTrace_1192248 : CollatzResearch.WordTrace tailWord_1192248 prefixEnd_1192248 204065427787252185972319 := by
  unfold tailWord_1192248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21742428492348295296256699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28989904656464393728342265 21742428492348295296256699)
  ·
    refine ⟨32613642738522442944385049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21742428492348295296256699 32613642738522442944385049)
    ·
      refine ⟨24460232053891832208288787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32613642738522442944385049 24460232053891832208288787)
      ·
        refine ⟨36690348080837748312433181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24460232053891832208288787 36690348080837748312433181)
        ·
          refine ⟨13758880530314155617162443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36690348080837748312433181 13758880530314155617162443)
          ·
            refine ⟨20638320795471233425743665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758880530314155617162443 20638320795471233425743665)
            ·
              refine ⟨15478740596603425069307749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20638320795471233425743665 15478740596603425069307749)
              ·
                refine ⟨2902263861863142200495203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15478740596603425069307749 2902263861863142200495203)
                ·
                  refine ⟨4353395792794713300742805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902263861863142200495203 4353395792794713300742805)
                  ·
                    refine ⟨204065427787252185972319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4353395792794713300742805 204065427787252185972319)
                    ·
                      rfl

theorem cell23_1192248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_1192248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192248 prefixEnd_1192248 := by exact prefixLift 1192248
  have htrace : WordTrace (prefixWord ++ tailWord_1192248) baseStart_1192248 baseEnd_1192248 := by
    simpa [prefixWord, tailWord_1192248, baseEnd_1192248] using wordTrace_append hprefix tailTrace_1192248
  have hstable : (prefixWord ++ tailWord_1192248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192248).length < 2 ^ (prefixWord ++ tailWord_1192248).sum := by decide
  have hdescent : baseEnd_1192248 < baseStart_1192248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192255 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_1192255 : Nat := 118140960795 + 1192255 * 2 ^ 59
def prefixEnd_1192255 : Nat := 4983230072969 + 3 ^ 40 * 1192255 * 2
def baseEnd_1192255 : Nat := 612199877726338030529425

theorem tailTrace_1192255 : CollatzResearch.WordTrace tailWord_1192255 prefixEnd_1192255 612199877726338030529425 := by
  unfold tailWord_1192255
  simp only [CollatzResearch.WordTrace]
  refine ⟨43485112295671230788018219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28990074863780820525345479 43485112295671230788018219)
  ·
    refine ⟨65227668443506846182027329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43485112295671230788018219 65227668443506846182027329)
    ·
      refine ⟨48920751332630134636520497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65227668443506846182027329 48920751332630134636520497)
      ·
        refine ⟨36690563499472600977390373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48920751332630134636520497 36690563499472600977390373)
        ·
          refine ⟨6879480656151112683260695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36690563499472600977390373 6879480656151112683260695)
          ·
            refine ⟨10319220984226669024891043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879480656151112683260695 10319220984226669024891043)
            ·
              refine ⟨15478831476340003537336565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10319220984226669024891043 15478831476340003537336565)
              ·
                refine ⟨1451140450906875331625303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15478831476340003537336565 1451140450906875331625303)
                ·
                  refine ⟨2176710676360312997437955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451140450906875331625303 2176710676360312997437955)
                  ·
                    refine ⟨3265066014540469496156933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2176710676360312997437955 3265066014540469496156933)
                    ·
                      refine ⟨612199877726338030529425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3265066014540469496156933 612199877726338030529425)
                      ·
                        rfl

theorem cell23_1192255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_1192255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192255 prefixEnd_1192255 := by exact prefixLift 1192255
  have htrace : WordTrace (prefixWord ++ tailWord_1192255) baseStart_1192255 baseEnd_1192255 := by
    simpa [prefixWord, tailWord_1192255, baseEnd_1192255] using wordTrace_append hprefix tailTrace_1192255
  have hstable : (prefixWord ++ tailWord_1192255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192255).length < 2 ^ (prefixWord ++ tailWord_1192255).sum := by decide
  have hdescent : baseEnd_1192255 < baseStart_1192255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192265 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_1192265 : Nat := 118140960795 + 1192265 * 2 ^ 59
def prefixEnd_1192265 : Nat := 4983230072969 + 3 ^ 40 * 1192265 * 2
def baseEnd_1192265 : Nat := 204068337510960997134793

theorem tailTrace_1192265 : CollatzResearch.WordTrace tailWord_1192265 prefixEnd_1192265 204068337510960997134793 := by
  unfold tailWord_1192265
  simp only [CollatzResearch.WordTrace]
  refine ⟨43485477025635002495882249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28990318017090001663921499 43485477025635002495882249)
  ·
    refine ⟨32614107769226251871911687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43485477025635002495882249 32614107769226251871911687)
    ·
      refine ⟨48921161653839377807867531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32614107769226251871911687 48921161653839377807867531)
      ·
        refine ⟨73381742480759066711801297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48921161653839377807867531 73381742480759066711801297)
        ·
          refine ⟨55036306860569300033850973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73381742480759066711801297 55036306860569300033850973)
          ·
            refine ⟨20638615072713487512694115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55036306860569300033850973 20638615072713487512694115)
            ·
              refine ⟨30957922609070231269041173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20638615072713487512694115 30957922609070231269041173)
              ·
                refine ⟨1451152622300167090736305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30957922609070231269041173 1451152622300167090736305)
                ·
                  refine ⟨1088364466725125318052229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1451152622300167090736305 1088364466725125318052229)
                  ·
                    refine ⟨204068337510960997134793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088364466725125318052229 204068337510960997134793)
                    ·
                      rfl

theorem cell23_1192265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_1192265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192265 prefixEnd_1192265 := by exact prefixLift 1192265
  have htrace : WordTrace (prefixWord ++ tailWord_1192265) baseStart_1192265 baseEnd_1192265 := by
    simpa [prefixWord, tailWord_1192265, baseEnd_1192265] using wordTrace_append hprefix tailTrace_1192265
  have hstable : (prefixWord ++ tailWord_1192265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192265).length < 2 ^ (prefixWord ++ tailWord_1192265).sum := by decide
  have hdescent : baseEnd_1192265 < baseStart_1192265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192268 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1192268 : Nat := 118140960795 + 1192268 * 2 ^ 59
def prefixEnd_1192268 : Nat := 4983230072969 + 3 ^ 40 * 1192268 * 2
def baseEnd_1192268 : Nat := 612206552974846479666865

theorem tailTrace_1192268 : CollatzResearch.WordTrace tailWord_1192268 prefixEnd_1192268 612206552974846479666865 := by
  unfold tailWord_1192268
  simp only [CollatzResearch.WordTrace]
  refine ⟨21742793222312067004120729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28990390963082756005494305 21742793222312067004120729)
  ·
    refine ⟨16307094916734050253090547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21742793222312067004120729 16307094916734050253090547)
    ·
      refine ⟨24460642375101075379635821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16307094916734050253090547 24460642375101075379635821)
      ·
        refine ⟨9172740890662903267363433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24460642375101075379635821 9172740890662903267363433)
        ·
          refine ⟨6879555667997177450522575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9172740890662903267363433 6879555667997177450522575)
          ·
            refine ⟨10319333501995766175783863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879555667997177450522575 10319333501995766175783863)
            ·
              refine ⟨15479000252993649263675795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10319333501995766175783863 15479000252993649263675795)
              ·
                refine ⟨23218500379490473895513693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15479000252993649263675795 23218500379490473895513693)
                ·
                  refine ⟨8706937642308927710817635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23218500379490473895513693 8706937642308927710817635)
                  ·
                    refine ⟨13060406463463391566226453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8706937642308927710817635 13060406463463391566226453)
                    ·
                      refine ⟨612206552974846479666865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13060406463463391566226453 612206552974846479666865)
                      ·
                        rfl

theorem cell23_1192268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1192268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192268 prefixEnd_1192268 := by exact prefixLift 1192268
  have htrace : WordTrace (prefixWord ++ tailWord_1192268) baseStart_1192268 baseEnd_1192268 := by
    simpa [prefixWord, tailWord_1192268, baseEnd_1192268] using wordTrace_append hprefix tailTrace_1192268
  have hstable : (prefixWord ++ tailWord_1192268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192268).length < 2 ^ (prefixWord ++ tailWord_1192268).sum := by decide
  have hdescent : baseEnd_1192268 < baseStart_1192268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192332 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 3, 3, 2]
def baseStart_1192332 : Nat := 118140960795 + 1192332 * 2 ^ 59
def prefixEnd_1192332 : Nat := 4983230072969 + 3 ^ 40 * 1192332 * 2
def baseEnd_1192332 : Nat := 612239415736734229266571

theorem tailTrace_1192332 : CollatzResearch.WordTrace tailWord_1192332 prefixEnd_1192332 612239415736734229266571 := by
  unfold tailWord_1192332
  simp only [CollatzResearch.WordTrace]
  refine ⟨21743960358196136469285625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28991947144261515292380833 21743960358196136469285625)
  ·
    refine ⟨16307970268647102351964219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21743960358196136469285625 16307970268647102351964219)
    ·
      refine ⟨24461955402970653527946329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16307970268647102351964219 24461955402970653527946329)
      ·
        refine ⟨18346466552227990145959747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24461955402970653527946329 18346466552227990145959747)
        ·
          refine ⟨27519699828341985218939621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18346466552227990145959747 27519699828341985218939621)
          ·
            refine ⟨5159943717814122228551179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27519699828341985218939621 5159943717814122228551179)
            ·
              refine ⟨7739915576721183342826769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159943717814122228551179 7739915576721183342826769)
              ·
                refine ⟨5804936682540887507120077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7739915576721183342826769 5804936682540887507120077)
                ·
                  refine ⟨2176851255952832815170029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5804936682540887507120077 2176851255952832815170029)
                  ·
                    refine ⟨816319220982312305688761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176851255952832815170029 816319220982312305688761)
                    ·
                      refine ⟨612239415736734229266571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816319220982312305688761 612239415736734229266571)
                      ·
                        rfl

theorem cell23_1192332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_1192332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192332 prefixEnd_1192332 := by exact prefixLift 1192332
  have htrace : WordTrace (prefixWord ++ tailWord_1192332) baseStart_1192332 baseEnd_1192332 := by
    simpa [prefixWord, tailWord_1192332, baseEnd_1192332] using wordTrace_append hprefix tailTrace_1192332
  have hstable : (prefixWord ++ tailWord_1192332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192332).length < 2 ^ (prefixWord ++ tailWord_1192332).sum := by decide
  have hdescent : baseEnd_1192332 < baseStart_1192332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192373 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_1192373 : Nat := 118140960795 + 1192373 * 2 ^ 59
def prefixEnd_1192373 : Nat := 4983230072969 + 3 ^ 40 * 1192373 * 2
def baseEnd_1192373 : Nat := 612260468443568568853883

theorem tailTrace_1192373 : CollatzResearch.WordTrace tailWord_1192373 prefixEnd_1192373 612260468443568568853883 := by
  unfold tailWord_1192373
  simp only [CollatzResearch.WordTrace]
  refine ⟨43489416109243736940813773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28992944072829157960542515 43489416109243736940813773)
  ·
    refine ⟨16308531040966401352805165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43489416109243736940813773 16308531040966401352805165)
    ·
      refine ⟨6115699140362400507301937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16308531040966401352805165 6115699140362400507301937)
      ·
        refine ⟨4586774355271800380476453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6115699140362400507301937 4586774355271800380476453)
        ·
          refine ⟨860020191613462571339335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4586774355271800380476453 860020191613462571339335)
          ·
            refine ⟨1290030287420193857009003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860020191613462571339335 1290030287420193857009003)
            ·
              refine ⟨1935045431130290785513505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290030287420193857009003 1935045431130290785513505)
              ·
                refine ⟨1451284073347718089135129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935045431130290785513505 1451284073347718089135129)
                ·
                  refine ⟨1088463055010788566851347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1451284073347718089135129 1088463055010788566851347)
                  ·
                    refine ⟨1632694582516182850277021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088463055010788566851347 1632694582516182850277021)
                    ·
                      refine ⟨612260468443568568853883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632694582516182850277021 612260468443568568853883)
                      ·
                        rfl

theorem cell23_1192373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_1192373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192373 prefixEnd_1192373 := by exact prefixLift 1192373
  have htrace : WordTrace (prefixWord ++ tailWord_1192373) baseStart_1192373 baseEnd_1192373 := by
    simpa [prefixWord, tailWord_1192373, baseEnd_1192373] using wordTrace_append hprefix tailTrace_1192373
  have hstable : (prefixWord ++ tailWord_1192373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192373).length < 2 ^ (prefixWord ++ tailWord_1192373).sum := by decide
  have hdescent : baseEnd_1192373 < baseStart_1192373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192375 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_1192375 : Nat := 118140960795 + 1192375 * 2 ^ 59
def prefixEnd_1192375 : Nat := 4983230072969 + 3 ^ 40 * 1192375 * 2
def baseEnd_1192375 : Nat := 612261495404877561028873

theorem tailTrace_1192375 : CollatzResearch.WordTrace tailWord_1192375 prefixEnd_1192375 612261495404877561028873 := by
  unfold tailWord_1192375
  simp only [CollatzResearch.WordTrace]
  refine ⟨43489489055236491282386579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28992992703490994188257719 43489489055236491282386579)
  ·
    refine ⟨65234233582854736923579869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43489489055236491282386579 65234233582854736923579869)
    ·
      refine ⟨24462837593570526346342451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65234233582854736923579869 24462837593570526346342451)
      ·
        refine ⟨36694256390355789519513677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24462837593570526346342451 36694256390355789519513677)
        ·
          refine ⟨13760346146383421069817629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36694256390355789519513677 13760346146383421069817629)
          ·
            refine ⟨5160129804893782901181611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13760346146383421069817629 5160129804893782901181611)
            ·
              refine ⟨7740194707340674351772417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160129804893782901181611 7740194707340674351772417)
              ·
                refine ⟨5805146030505505763829313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7740194707340674351772417 5805146030505505763829313)
                ·
                  refine ⟨4353859522879129322871985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805146030505505763829313 4353859522879129322871985)
                  ·
                    refine ⟨3265394642159346992153989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4353859522879129322871985 3265394642159346992153989)
                    ·
                      refine ⟨612261495404877561028873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3265394642159346992153989 612261495404877561028873)
                      ·
                        rfl

theorem cell23_1192375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_1192375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192375 prefixEnd_1192375 := by exact prefixLift 1192375
  have htrace : WordTrace (prefixWord ++ tailWord_1192375) baseStart_1192375 baseEnd_1192375 := by
    simpa [prefixWord, tailWord_1192375, baseEnd_1192375] using wordTrace_append hprefix tailTrace_1192375
  have hstable : (prefixWord ++ tailWord_1192375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192375).length < 2 ^ (prefixWord ++ tailWord_1192375).sum := by decide
  have hdescent : baseEnd_1192375 < baseStart_1192375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192396 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1192396 : Nat := 118140960795 + 1192396 * 2 ^ 59
def prefixEnd_1192396 : Nat := 4983230072969 + 3 ^ 40 * 1192396 * 2
def baseEnd_1192396 : Nat := 612272278498621978866277

theorem tailTrace_1192396 : CollatzResearch.WordTrace tailWord_1192396 prefixEnd_1192396 612272278498621978866277 := by
  unfold tailWord_1192396
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745127494080205934450521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28993503325440274579267361 21745127494080205934450521)
  ·
    refine ⟨16308845620560154450837891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21745127494080205934450521 16308845620560154450837891)
    ·
      refine ⟨24463268430840231676256837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16308845620560154450837891 24463268430840231676256837)
      ·
        refine ⟨4586862830782543439298157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24463268430840231676256837 4586862830782543439298157)
        ·
          refine ⟨1720073561543453789736809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4586862830782543439298157 1720073561543453789736809)
          ·
            refine ⟨1290055171157590342302607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1720073561543453789736809 1290055171157590342302607)
            ·
              refine ⟨1935082756736385513453911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290055171157590342302607 1935082756736385513453911)
              ·
                refine ⟨2902624135104578270180867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935082756736385513453911 2902624135104578270180867)
                ·
                  refine ⟨4353936202656867405271301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902624135104578270180867 4353936202656867405271301)
                  ·
                    refine ⟨816363037998162638488369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353936202656867405271301 816363037998162638488369)
                    ·
                      refine ⟨612272278498621978866277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816363037998162638488369 612272278498621978866277)
                      ·
                        rfl

theorem cell23_1192396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1192396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192396 prefixEnd_1192396 := by exact prefixLift 1192396
  have htrace : WordTrace (prefixWord ++ tailWord_1192396) baseStart_1192396 baseEnd_1192396 := by
    simpa [prefixWord, tailWord_1192396, baseEnd_1192396] using wordTrace_append hprefix tailTrace_1192396
  have hstable : (prefixWord ++ tailWord_1192396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192396).length < 2 ^ (prefixWord ++ tailWord_1192396).sum := by decide
  have hdescent : baseEnd_1192396 < baseStart_1192396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192415 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 7]
def baseStart_1192415 : Nat := 118140960795 + 1192415 * 2 ^ 59
def prefixEnd_1192415 : Nat := 4983230072969 + 3 ^ 40 * 1192415 * 2
def baseEnd_1192415 : Nat := 204094011543685801509563

theorem tailTrace_1192415 : CollatzResearch.WordTrace tailWord_1192415 prefixEnd_1192415 204094011543685801509563 := by
  unfold tailWord_1192415
  simp only [CollatzResearch.WordTrace]
  refine ⟨43490947975091578113842699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28993965316727718742561799 43490947975091578113842699)
  ·
    refine ⟨65236421962637367170764049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43490947975091578113842699 65236421962637367170764049)
    ·
      refine ⟨48927316471978025378073037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65236421962637367170764049 48927316471978025378073037)
      ·
        refine ⟨18347743676991759516777389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48927316471978025378073037 18347743676991759516777389)
        ·
          refine ⟨6880403878871909818791521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18347743676991759516777389 6880403878871909818791521)
          ·
            refine ⟨5160302909153932364093641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6880403878871909818791521 5160302909153932364093641)
            ·
              refine ⟨3870227181865449273070231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160302909153932364093641 3870227181865449273070231)
              ·
                refine ⟨5805340772798173909605347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870227181865449273070231 5805340772798173909605347)
                ·
                  refine ⟨8708011159197260864408021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5805340772798173909605347 8708011159197260864408021)
                  ·
                    refine ⟨204094011543685801509563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8708011159197260864408021 204094011543685801509563)
                    ·
                      rfl

theorem cell23_1192415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_1192415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192415 prefixEnd_1192415 := by exact prefixLift 1192415
  have htrace : WordTrace (prefixWord ++ tailWord_1192415) baseStart_1192415 baseEnd_1192415 := by
    simpa [prefixWord, tailWord_1192415, baseEnd_1192415] using wordTrace_append hprefix tailTrace_1192415
  have hstable : (prefixWord ++ tailWord_1192415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192415).length < 2 ^ (prefixWord ++ tailWord_1192415).sum := by decide
  have hdescent : baseEnd_1192415 < baseStart_1192415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192479 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 1, 4]
def baseStart_1192479 : Nat := 118140960795 + 1192479 * 2 ^ 59
def prefixEnd_1192479 : Nat := 4983230072969 + 3 ^ 40 * 1192479 * 2
def baseEnd_1192479 : Nat := 204104965797648384709465

theorem tailTrace_1192479 : CollatzResearch.WordTrace tailWord_1192479 prefixEnd_1192479 204104965797648384709465 := by
  unfold tailWord_1192479
  simp only [CollatzResearch.WordTrace]
  refine ⟨43493282246859717044172491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28995521497906478029448327 43493282246859717044172491)
  ·
    refine ⟨65239923370289575566258737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43493282246859717044172491 65239923370289575566258737)
    ·
      refine ⟨48929942527717181674694053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65239923370289575566258737 48929942527717181674694053)
      ·
        refine ⟨9174364223946971564005135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48929942527717181674694053 9174364223946971564005135)
        ·
          refine ⟨13761546335920457346007703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9174364223946971564005135 13761546335920457346007703)
          ·
            refine ⟨20642319503880686019011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13761546335920457346007703 20642319503880686019011555)
            ·
              refine ⟨30963479255821029028517333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20642319503880686019011555 30963479255821029028517333)
              ·
                refine ⟨725706545058305367855875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30963479255821029028517333 725706545058305367855875)
                ·
                  refine ⟨1088559817587458051783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725706545058305367855875 1088559817587458051783813)
                  ·
                    refine ⟨204104965797648384709465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088559817587458051783813 204104965797648384709465)
                    ·
                      rfl

theorem cell23_1192479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 4].length) (baseStart_1192479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192479 prefixEnd_1192479 := by exact prefixLift 1192479
  have htrace : WordTrace (prefixWord ++ tailWord_1192479) baseStart_1192479 baseEnd_1192479 := by
    simpa [prefixWord, tailWord_1192479, baseEnd_1192479] using wordTrace_append hprefix tailTrace_1192479
  have hstable : (prefixWord ++ tailWord_1192479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192479).length < 2 ^ (prefixWord ++ tailWord_1192479).sum := by decide
  have hdescent : baseEnd_1192479 < baseStart_1192479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192496 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 1, 4]
def baseStart_1192496 : Nat := 118140960795 + 1192496 * 2 ^ 59
def prefixEnd_1192496 : Nat := 4983230072969 + 3 ^ 40 * 1192496 * 2
def baseEnd_1192496 : Nat := 204107875521357195871939

theorem tailTrace_1192496 : CollatzResearch.WordTrace tailWord_1192496 prefixEnd_1192496 204107875521357195871939 := by
  unfold tailWord_1192496
  simp only [CollatzResearch.WordTrace]
  refine ⟨21746951143899064473770671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28995934858532085965027561 21746951143899064473770671)
  ·
    refine ⟨32620426715848596710656007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21746951143899064473770671 32620426715848596710656007)
    ·
      refine ⟨48930640073772895065984011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32620426715848596710656007 48930640073772895065984011)
      ·
        refine ⟨73395960110659342598976017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48930640073772895065984011 73395960110659342598976017)
        ·
          refine ⟨55046970082994506949232013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73395960110659342598976017 55046970082994506949232013)
          ·
            refine ⟨20642613781122940105962005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55046970082994506949232013 20642613781122940105962005)
            ·
              refine ⟨967622520990137817466969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20642613781122940105962005 967622520990137817466969)
              ·
                refine ⟨725716890742603363100227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967622520990137817466969 725716890742603363100227)
                ·
                  refine ⟨1088575336113905044650341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725716890742603363100227 1088575336113905044650341)
                  ·
                    refine ⟨204107875521357195871939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088575336113905044650341 204107875521357195871939)
                    ·
                      rfl

theorem cell23_1192496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 4].length) (baseStart_1192496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192496 prefixEnd_1192496 := by exact prefixLift 1192496
  have htrace : WordTrace (prefixWord ++ tailWord_1192496) baseStart_1192496 baseEnd_1192496 := by
    simpa [prefixWord, tailWord_1192496, baseEnd_1192496] using wordTrace_append hprefix tailTrace_1192496
  have hstable : (prefixWord ++ tailWord_1192496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192496).length < 2 ^ (prefixWord ++ tailWord_1192496).sum := by decide
  have hdescent : baseEnd_1192496 < baseStart_1192496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192519 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_1192519 : Nat := 118140960795 + 1192519 * 2 ^ 59
def prefixEnd_1192519 : Nat := 4983230072969 + 3 ^ 40 * 1192519 * 2
def baseEnd_1192519 : Nat := 612335436619124997628211

theorem tailTrace_1192519 : CollatzResearch.WordTrace tailWord_1192519 prefixEnd_1192519 612335436619124997628211 := by
  unfold tailWord_1192519
  simp only [CollatzResearch.WordTrace]
  refine ⟨43494741166714803875628611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28996494111143202583752407 43494741166714803875628611)
  ·
    refine ⟨65242111750072205813442917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43494741166714803875628611 65242111750072205813442917)
    ·
      refine ⟨12232895953138538590020547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65242111750072205813442917 12232895953138538590020547)
      ·
        refine ⟨18349343929707807885030821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12232895953138538590020547 18349343929707807885030821)
        ·
          refine ⟨3440501986820213978443279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18349343929707807885030821 3440501986820213978443279)
          ·
            refine ⟨5160752980230320967664919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440501986820213978443279 5160752980230320967664919)
            ·
              refine ⟨7741129470345481451497379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160752980230320967664919 7741129470345481451497379)
              ·
                refine ⟨11611694205518222177246069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7741129470345481451497379 11611694205518222177246069)
                ·
                  refine ⟨1088596331767333329116819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11611694205518222177246069 1088596331767333329116819)
                  ·
                    refine ⟨1632894497650999993675229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088596331767333329116819 1632894497650999993675229)
                    ·
                      refine ⟨612335436619124997628211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632894497650999993675229 612335436619124997628211)
                      ·
                        rfl

theorem cell23_1192519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_1192519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192519 prefixEnd_1192519 := by exact prefixLift 1192519
  have htrace : WordTrace (prefixWord ++ tailWord_1192519) baseStart_1192519 baseEnd_1192519 := by
    simpa [prefixWord, tailWord_1192519, baseEnd_1192519] using wordTrace_append hprefix tailTrace_1192519
  have hstable : (prefixWord ++ tailWord_1192519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192519).length < 2 ^ (prefixWord ++ tailWord_1192519).sum := by decide
  have hdescent : baseEnd_1192519 < baseStart_1192519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192522 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1192522 : Nat := 118140960795 + 1192522 * 2 ^ 59
def prefixEnd_1192522 : Nat := 4983230072969 + 3 ^ 40 * 1192522 * 2
def baseEnd_1192522 : Nat := 204112325687029495296899

theorem tailTrace_1192522 : CollatzResearch.WordTrace tailWord_1192522 prefixEnd_1192522 204112325687029495296899 := by
  unfold tailWord_1192522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873712646425983846996955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28996567057135956925325213 10873712646425983846996955)
  ·
    refine ⟨16310568969638975770495433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10873712646425983846996955 16310568969638975770495433)
    ·
      refine ⟨12232926727229231827871575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16310568969638975770495433 12232926727229231827871575)
      ·
        refine ⟨18349390090843847741807363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12232926727229231827871575 18349390090843847741807363)
        ·
          refine ⟨27524085136265771612711045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18349390090843847741807363 27524085136265771612711045)
          ·
            refine ⟨5160765963049832177383321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27524085136265771612711045 5160765963049832177383321)
            ·
              refine ⟨3870574472287374133037491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160765963049832177383321 3870574472287374133037491)
              ·
                refine ⟨5805861708431061199556237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870574472287374133037491 5805861708431061199556237)
                ·
                  refine ⟨2177198140661647949833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5805861708431061199556237 2177198140661647949833589)
                  ·
                    refine ⟨204112325687029495296899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2177198140661647949833589 204112325687029495296899)
                    ·
                      rfl

theorem cell23_1192522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1192522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192522 prefixEnd_1192522 := by exact prefixLift 1192522
  have htrace : WordTrace (prefixWord ++ tailWord_1192522) baseStart_1192522 baseEnd_1192522 := by
    simpa [prefixWord, tailWord_1192522, baseEnd_1192522] using wordTrace_append hprefix tailTrace_1192522
  have hstable : (prefixWord ++ tailWord_1192522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192522).length < 2 ^ (prefixWord ++ tailWord_1192522).sum := by decide
  have hdescent : baseEnd_1192522 < baseStart_1192522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192529 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_1192529 : Nat := 118140960795 + 1192529 * 2 ^ 59
def prefixEnd_1192529 : Nat := 4983230072969 + 3 ^ 40 * 1192529 * 2
def baseEnd_1192529 : Nat := 612340571425669958503165

theorem tailTrace_1192529 : CollatzResearch.WordTrace tailWord_1192529 prefixEnd_1192529 612340571425669958503165 := by
  unfold tailWord_1192529
  simp only [CollatzResearch.WordTrace]
  refine ⟨43495105896678575583492641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28996737264452383722328427 43495105896678575583492641)
  ·
    refine ⟨32621329422508931687619481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43495105896678575583492641 32621329422508931687619481)
    ·
      refine ⟨24465997066881698765714611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32621329422508931687619481 24465997066881698765714611)
      ·
        refine ⟨36698995600322548148571917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24465997066881698765714611 36698995600322548148571917)
        ·
          refine ⟨13762123350120955555714469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36698995600322548148571917 13762123350120955555714469)
          ·
            refine ⟨2580398128147679166696463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13762123350120955555714469 2580398128147679166696463)
            ·
              refine ⟨3870597192221518750044695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580398128147679166696463 3870597192221518750044695)
              ·
                refine ⟨5805895788332278125067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870597192221518750044695 5805895788332278125067043)
                ·
                  refine ⟨8708843682498417187600565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5805895788332278125067043 8708843682498417187600565)
                  ·
                    refine ⟨816454095234226611337553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8708843682498417187600565 816454095234226611337553)
                    ·
                      refine ⟨612340571425669958503165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816454095234226611337553 612340571425669958503165)
                      ·
                        rfl

theorem cell23_1192529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_1192529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192529 prefixEnd_1192529 := by exact prefixLift 1192529
  have htrace : WordTrace (prefixWord ++ tailWord_1192529) baseStart_1192529 baseEnd_1192529 := by
    simpa [prefixWord, tailWord_1192529, baseEnd_1192529] using wordTrace_append hprefix tailTrace_1192529
  have hstable : (prefixWord ++ tailWord_1192529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192529).length < 2 ^ (prefixWord ++ tailWord_1192529).sum := by decide
  have hdescent : baseEnd_1192529 < baseStart_1192529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192536 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 1, 1, 3]
def baseStart_1192536 : Nat := 118140960795 + 1192536 * 2 ^ 59
def prefixEnd_1192536 : Nat := 4983230072969 + 3 ^ 40 * 1192536 * 2
def baseEnd_1192536 : Nat := 612344165790251431115633

theorem tailTrace_1192536 : CollatzResearch.WordTrace tailWord_1192536 prefixEnd_1192536 612344165790251431115633 := by
  unfold tailWord_1192536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21747680603826607889498731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28996907471768810519331641 21747680603826607889498731)
  ·
    refine ⟨32621520905739911834248097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21747680603826607889498731 32621520905739911834248097)
    ·
      refine ⟨24466140679304933875686073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32621520905739911834248097 24466140679304933875686073)
      ·
        refine ⟨18349605509478700406764555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24466140679304933875686073 18349605509478700406764555)
        ·
          refine ⟨27524408264218050610146833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18349605509478700406764555 27524408264218050610146833)
          ·
            refine ⟨20643306198163537957610125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27524408264218050610146833 20643306198163537957610125)
            ·
              refine ⟨7741239824311326734103797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20643306198163537957610125 7741239824311326734103797)
              ·
                refine ⟨725741233529186881322231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7741239824311326734103797 725741233529186881322231)
                ·
                  refine ⟨1088611850293780321983347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725741233529186881322231 1088611850293780321983347)
                  ·
                    refine ⟨1632917775440670482975021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088611850293780321983347 1632917775440670482975021)
                    ·
                      refine ⟨612344165790251431115633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632917775440670482975021 612344165790251431115633)
                      ·
                        rfl

theorem cell23_1192536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_1192536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192536 prefixEnd_1192536 := by exact prefixLift 1192536
  have htrace : WordTrace (prefixWord ++ tailWord_1192536) baseStart_1192536 baseEnd_1192536 := by
    simpa [prefixWord, tailWord_1192536, baseEnd_1192536] using wordTrace_append hprefix tailTrace_1192536
  have hstable : (prefixWord ++ tailWord_1192536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192536).length < 2 ^ (prefixWord ++ tailWord_1192536).sum := by decide
  have hdescent : baseEnd_1192536 < baseStart_1192536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192569 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_1192569 : Nat := 118140960795 + 1192569 * 2 ^ 59
def prefixEnd_1192569 : Nat := 4983230072969 + 3 ^ 40 * 1192569 * 2
def baseEnd_1192569 : Nat := 204120370217283267334327

theorem tailTrace_1192569 : CollatzResearch.WordTrace tailWord_1192569 prefixEnd_1192569 204120370217283267334327 := by
  unfold tailWord_1192569
  simp only [CollatzResearch.WordTrace]
  refine ⟨43496564816533662414948761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28997709877689108276632507 43496564816533662414948761)
  ·
    refine ⟨32622423612400246811211571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43496564816533662414948761 32622423612400246811211571)
    ·
      refine ⟨48933635418600370216817357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32622423612400246811211571 48933635418600370216817357)
      ·
        refine ⟨18350113281975138831306509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48933635418600370216817357 18350113281975138831306509)
        ·
          refine ⟨6881292480740677061739941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18350113281975138831306509 6881292480740677061739941)
          ·
            refine ⟨1290242340138876949076239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6881292480740677061739941 1290242340138876949076239)
            ·
              refine ⟨1935363510208315423614359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290242340138876949076239 1935363510208315423614359)
              ·
                refine ⟨2903045265312473135421539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935363510208315423614359 2903045265312473135421539)
                ·
                  refine ⟨4354567897968709703132309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903045265312473135421539 4354567897968709703132309)
                  ·
                    refine ⟨204120370217283267334327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4354567897968709703132309 204120370217283267334327)
                    ·
                      rfl

theorem cell23_1192569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_1192569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192569 prefixEnd_1192569 := by exact prefixLift 1192569
  have htrace : WordTrace (prefixWord ++ tailWord_1192569) baseStart_1192569 baseEnd_1192569 := by
    simpa [prefixWord, tailWord_1192569, baseEnd_1192569] using wordTrace_append hprefix tailTrace_1192569
  have hstable : (prefixWord ++ tailWord_1192569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192569).length < 2 ^ (prefixWord ++ tailWord_1192569).sum := by decide
  have hdescent : baseEnd_1192569 < baseStart_1192569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192576 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2]
def baseStart_1192576 : Nat := 118140960795 + 1192576 * 2 ^ 59
def prefixEnd_1192576 : Nat := 4983230072969 + 3 ^ 40 * 1192576 * 2
def baseEnd_1192576 : Nat := 612364705016431274615449

theorem tailTrace_1192576 : CollatzResearch.WordTrace tailWord_1192576 prefixEnd_1192576 612364705016431274615449 := by
  unfold tailWord_1192576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21748410063754151305226791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28997880085005535073635721 21748410063754151305226791)
  ·
    refine ⟨32622615095631226957840187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21748410063754151305226791 32622615095631226957840187)
    ·
      refine ⟨48933922643446840436760281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32622615095631226957840187 48933922643446840436760281)
      ·
        refine ⟨36700441982585130327570211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48933922643446840436760281 36700441982585130327570211)
        ·
          refine ⟨55050662973877695491355317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36700441982585130327570211 55050662973877695491355317)
          ·
            refine ⟨5160999653801033952314561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55050662973877695491355317 5160999653801033952314561)
            ·
              refine ⟨3870749740350775464235921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5160999653801033952314561 3870749740350775464235921)
              ·
                refine ⟨2903062305263081598176941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870749740350775464235921 2903062305263081598176941)
                ·
                  refine ⟨1088648364473655599316353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2903062305263081598176941 1088648364473655599316353)
                  ·
                    refine ⟨816486273355241699487265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088648364473655599316353 816486273355241699487265)
                    ·
                      refine ⟨612364705016431274615449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816486273355241699487265 612364705016431274615449)
                      ·
                        rfl

theorem cell23_1192576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_1192576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192576 prefixEnd_1192576 := by exact prefixLift 1192576
  have htrace : WordTrace (prefixWord ++ tailWord_1192576) baseStart_1192576 baseEnd_1192576 := by
    simpa [prefixWord, tailWord_1192576, baseEnd_1192576] using wordTrace_append hprefix tailTrace_1192576
  have hstable : (prefixWord ++ tailWord_1192576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192576).length < 2 ^ (prefixWord ++ tailWord_1192576).sum := by decide
  have hdescent : baseEnd_1192576 < baseStart_1192576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192579 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 3]
def baseStart_1192579 : Nat := 118140960795 + 1192579 * 2 ^ 59
def prefixEnd_1192579 : Nat := 4983230072969 + 3 ^ 40 * 1192579 * 2
def baseEnd_1192579 : Nat := 612366245458394762877935

theorem tailTrace_1192579 : CollatzResearch.WordTrace tailWord_1192579 prefixEnd_1192579 612366245458394762877935 := by
  unfold tailWord_1192579
  simp only [CollatzResearch.WordTrace]
  refine ⟨43496929546497434122812791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28997953030998289415208527 43496929546497434122812791)
  ·
    refine ⟨65245394319746151184219187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43496929546497434122812791 65245394319746151184219187)
    ·
      refine ⟨97868091479619226776328781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65245394319746151184219187 97868091479619226776328781)
      ·
        refine ⟨36700534304857210041123293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97868091479619226776328781 36700534304857210041123293)
        ·
          refine ⟨13762700364321453765421235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36700534304857210041123293 13762700364321453765421235)
          ·
            refine ⟨20644050546482180648131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13762700364321453765421235 20644050546482180648131853)
            ·
              refine ⟨7741518954930817743049445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20644050546482180648131853 7741518954930817743049445)
              ·
                refine ⟨1451534804049528326821771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7741518954930817743049445 1451534804049528326821771)
                ·
                  refine ⟨2177302206074292490232657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451534804049528326821771 2177302206074292490232657)
                  ·
                    refine ⟨1632976654555719367674493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177302206074292490232657 1632976654555719367674493)
                    ·
                      refine ⟨612366245458394762877935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1632976654555719367674493 612366245458394762877935)
                      ·
                        rfl

theorem cell23_1192579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_1192579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192579 prefixEnd_1192579 := by exact prefixLift 1192579
  have htrace : WordTrace (prefixWord ++ tailWord_1192579) baseStart_1192579 baseEnd_1192579 := by
    simpa [prefixWord, tailWord_1192579, baseEnd_1192579] using wordTrace_append hprefix tailTrace_1192579
  have hstable : (prefixWord ++ tailWord_1192579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192579).length < 2 ^ (prefixWord ++ tailWord_1192579).sum := by decide
  have hdescent : baseEnd_1192579 < baseStart_1192579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192596 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1192596 : Nat := 118140960795 + 1192596 * 2 ^ 59
def prefixEnd_1192596 : Nat := 4983230072969 + 3 ^ 40 * 1192596 * 2
def baseEnd_1192596 : Nat := 612374974629521196365357

theorem tailTrace_1192596 : CollatzResearch.WordTrace tailWord_1192596 prefixEnd_1192596 612374974629521196365357 := by
  unfold tailWord_1192596
  simp only [CollatzResearch.WordTrace]
  refine ⟨21748774793717923013090821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28998366391623897350787761 21748774793717923013090821)
  ·
    refine ⟨4077895273822110564954529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21748774793717923013090821 4077895273822110564954529)
    ·
      refine ⟨3058421455366582923715897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4077895273822110564954529 3058421455366582923715897)
      ·
        refine ⟨2293816091524937192786923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3058421455366582923715897 2293816091524937192786923)
        ·
          refine ⟨3440724137287405789180385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293816091524937192786923 3440724137287405789180385)
          ·
            refine ⟨2580543102965554341885289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440724137287405789180385 2580543102965554341885289)
            ·
              refine ⟨1935407327224165756413967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580543102965554341885289 1935407327224165756413967)
              ·
                refine ⟨2903110990836248634620951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935407327224165756413967 2903110990836248634620951)
                ·
                  refine ⟨4354666486254372951931427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903110990836248634620951 4354666486254372951931427)
                  ·
                    refine ⟨6531999729381559427897141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4354666486254372951931427 6531999729381559427897141)
                    ·
                      refine ⟨612374974629521196365357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6531999729381559427897141 612374974629521196365357)
                      ·
                        rfl

theorem cell23_1192596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1192596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192596 prefixEnd_1192596 := by exact prefixLift 1192596
  have htrace : WordTrace (prefixWord ++ tailWord_1192596) baseStart_1192596 baseEnd_1192596 := by
    simpa [prefixWord, tailWord_1192596, baseEnd_1192596] using wordTrace_append hprefix tailTrace_1192596
  have hstable : (prefixWord ++ tailWord_1192596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192596).length < 2 ^ (prefixWord ++ tailWord_1192596).sum := by decide
  have hdescent : baseEnd_1192596 < baseStart_1192596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192612 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1192612 : Nat := 118140960795 + 1192612 * 2 ^ 59
def prefixEnd_1192612 : Nat := 4983230072969 + 3 ^ 40 * 1192612 * 2
def baseEnd_1192612 : Nat := 204127730106664377921761

theorem tailTrace_1192612 : CollatzResearch.WordTrace tailWord_1192612 prefixEnd_1192612 204127730106664377921761 := by
  unfold tailWord_1192612
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749066577688940379382045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28998755436918587172509393 21749066577688940379382045)
  ·
    refine ⟨8155899966633352642268267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21749066577688940379382045 8155899966633352642268267)
    ·
      refine ⟨12233849949950028963402401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8155899966633352642268267 12233849949950028963402401)
      ·
        refine ⟨9175387462462521722551801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12233849949950028963402401 9175387462462521722551801)
        ·
          refine ⟨6881540596846891291913851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9175387462462521722551801 6881540596846891291913851)
          ·
            refine ⟨10322310895270336937870777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6881540596846891291913851 10322310895270336937870777)
            ·
              refine ⟨7741733171452752703403083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10322310895270336937870777 7741733171452752703403083)
              ·
                refine ⟨11612599757179129055104625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7741733171452752703403083 11612599757179129055104625)
                ·
                  refine ⟨8709449817884346791328469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11612599757179129055104625 8709449817884346791328469)
                  ·
                    refine ⟨204127730106664377921761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8709449817884346791328469 204127730106664377921761)
                    ·
                      rfl

theorem cell23_1192612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1192612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192612 prefixEnd_1192612 := by exact prefixLift 1192612
  have htrace : WordTrace (prefixWord ++ tailWord_1192612) baseStart_1192612 baseEnd_1192612 := by
    simpa [prefixWord, tailWord_1192612, baseEnd_1192612] using wordTrace_append hprefix tailTrace_1192612
  have hstable : (prefixWord ++ tailWord_1192612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192612).length < 2 ^ (prefixWord ++ tailWord_1192612).sum := by decide
  have hdescent : baseEnd_1192612 < baseStart_1192612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192636 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_1192636 : Nat := 118140960795 + 1192636 * 2 ^ 59
def prefixEnd_1192636 : Nat := 4983230072969 + 3 ^ 40 * 1192636 * 2
def baseEnd_1192636 : Nat := 612395513855701039865173

theorem tailTrace_1192636 : CollatzResearch.WordTrace tailWord_1192636 prefixEnd_1192636 612395513855701039865173 := by
  unfold tailWord_1192636
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749504253645466428818881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28999339004860621905091841 21749504253645466428818881)
  ·
    refine ⟨16312128190234099821614161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21749504253645466428818881 16312128190234099821614161)
    ·
      refine ⟨12234096142675574866210621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16312128190234099821614161 12234096142675574866210621)
      ·
        refine ⟨4587786053503340574828983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12234096142675574866210621 4587786053503340574828983)
        ·
          refine ⟨6881679080255010862243475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587786053503340574828983 6881679080255010862243475)
          ·
            refine ⟨10322518620382516293365213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6881679080255010862243475 10322518620382516293365213)
            ·
              refine ⟨3870944482643443610011955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10322518620382516293365213 3870944482643443610011955)
              ·
                refine ⟨5806416723965165415017933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870944482643443610011955 5806416723965165415017933)
                ·
                  refine ⟨2177406271486937030631725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5806416723965165415017933 2177406271486937030631725)
                  ·
                    refine ⟨816527351807601386486897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2177406271486937030631725 816527351807601386486897)
                    ·
                      refine ⟨612395513855701039865173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816527351807601386486897 612395513855701039865173)
                      ·
                        rfl

theorem cell23_1192636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_1192636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192636 prefixEnd_1192636 := by exact prefixLift 1192636
  have htrace : WordTrace (prefixWord ++ tailWord_1192636) baseStart_1192636 baseEnd_1192636 := by
    simpa [prefixWord, tailWord_1192636, baseEnd_1192636] using wordTrace_append hprefix tailTrace_1192636
  have hstable : (prefixWord ++ tailWord_1192636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192636).length < 2 ^ (prefixWord ++ tailWord_1192636).sum := by decide
  have hdescent : baseEnd_1192636 < baseStart_1192636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192660 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1192660 : Nat := 118140960795 + 1192660 * 2 ^ 59
def prefixEnd_1192660 : Nat := 4983230072969 + 3 ^ 40 * 1192660 * 2
def baseEnd_1192660 : Nat := 612407837391408945965063

theorem tailTrace_1192660 : CollatzResearch.WordTrace tailWord_1192660 prefixEnd_1192660 612407837391408945965063 := by
  unfold tailWord_1192660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749941929601992478255717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28999922572802656637674289 21749941929601992478255717)
  ·
    refine ⟨4078114111800373589672947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21749941929601992478255717 4078114111800373589672947)
    ·
      refine ⟨6117171167700560384509421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078114111800373589672947 6117171167700560384509421)
      ·
        refine ⟨2293939187887710144191033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6117171167700560384509421 2293939187887710144191033)
        ·
          refine ⟨1720454390915782608143275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2293939187887710144191033 1720454390915782608143275)
          ·
            refine ⟨2580681586373673912214913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720454390915782608143275 2580681586373673912214913)
            ·
              refine ⟨1935511189780255434161185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580681586373673912214913 1935511189780255434161185)
              ·
                refine ⟨1451633392335191575620889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935511189780255434161185 1451633392335191575620889)
                ·
                  refine ⟨1088725044251393681715667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1451633392335191575620889 1088725044251393681715667)
                  ·
                    refine ⟨1633087566377090522573501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088725044251393681715667 1633087566377090522573501)
                    ·
                      refine ⟨612407837391408945965063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1633087566377090522573501 612407837391408945965063)
                      ·
                        rfl

theorem cell23_1192660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1192660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192660 prefixEnd_1192660 := by exact prefixLift 1192660
  have htrace : WordTrace (prefixWord ++ tailWord_1192660) baseStart_1192660 baseEnd_1192660 := by
    simpa [prefixWord, tailWord_1192660, baseEnd_1192660] using wordTrace_append hprefix tailTrace_1192660
  have hstable : (prefixWord ++ tailWord_1192660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192660).length < 2 ^ (prefixWord ++ tailWord_1192660).sum := by decide
  have hdescent : baseEnd_1192660 < baseStart_1192660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192661 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1192661 : Nat := 118140960795 + 1192661 * 2 ^ 59
def prefixEnd_1192661 : Nat := 4983230072969 + 3 ^ 40 * 1192661 * 2
def baseEnd_1192661 : Nat := 612408350872063442052559

theorem tailTrace_1192661 : CollatzResearch.WordTrace tailWord_1192661 prefixEnd_1192661 612408350872063442052559 := by
  unfold tailWord_1192661
  simp only [CollatzResearch.WordTrace]
  refine ⟨43499920332200362127297837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28999946888133574751531891 43499920332200362127297837)
  ·
    refine ⟨16312470124575135797736689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43499920332200362127297837 16312470124575135797736689)
    ·
      refine ⟨12234352593431351848302517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16312470124575135797736689 12234352593431351848302517)
      ·
        refine ⟨1146970555634189235778361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12234352593431351848302517 1146970555634189235778361)
        ·
          refine ⟨860227916725641926833771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146970555634189235778361 860227916725641926833771)
          ·
            refine ⟨1290341875088462890250657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860227916725641926833771 1290341875088462890250657)
            ·
              refine ⟨967756406316347167687993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290341875088462890250657 967756406316347167687993)
              ·
                refine ⟨725817304737260375765995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967756406316347167687993 725817304737260375765995)
                ·
                  refine ⟨1088725957105890563648993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725817304737260375765995 1088725957105890563648993)
                  ·
                    refine ⟨816544467829417922736745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088725957105890563648993 816544467829417922736745)
                    ·
                      refine ⟨612408350872063442052559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816544467829417922736745 612408350872063442052559)
                      ·
                        rfl

theorem cell23_1192661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1192661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192661 prefixEnd_1192661 := by exact prefixLift 1192661
  have htrace : WordTrace (prefixWord ++ tailWord_1192661) baseStart_1192661 baseEnd_1192661 := by
    simpa [prefixWord, tailWord_1192661, baseEnd_1192661] using wordTrace_append hprefix tailTrace_1192661
  have hstable : (prefixWord ++ tailWord_1192661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192661).length < 2 ^ (prefixWord ++ tailWord_1192661).sum := by decide
  have hdescent : baseEnd_1192661 < baseStart_1192661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192672 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 7]
def baseStart_1192672 : Nat := 118140960795 + 1192672 * 2 ^ 59
def prefixEnd_1192672 : Nat := 4983230072969 + 3 ^ 40 * 1192672 * 2
def baseEnd_1192672 : Nat := 68045999906584766557223

theorem tailTrace_1192672 : CollatzResearch.WordTrace tailWord_1192672 prefixEnd_1192672 68045999906584766557223 := by
  unfold tailWord_1192672
  simp only [CollatzResearch.WordTrace]
  refine ⟨21750160767580255502974135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29000214356773674003965513 21750160767580255502974135)
  ·
    refine ⟨32625241151370383254461203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21750160767580255502974135 32625241151370383254461203)
    ·
      refine ⟨48937861727055574881691805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32625241151370383254461203 48937861727055574881691805)
      ·
        refine ⟨18351698147645840580634427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48937861727055574881691805 18351698147645840580634427)
        ·
          refine ⟨27527547221468760870951641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18351698147645840580634427 27527547221468760870951641)
          ·
            refine ⟨20645660416101570653213731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27527547221468760870951641 20645660416101570653213731)
            ·
              refine ⟨30968490624152355979820597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20645660416101570653213731 30968490624152355979820597)
              ·
                refine ⟨2903295996014283373108181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30968490624152355979820597 2903295996014283373108181)
                ·
                  refine ⟨68045999906584766557223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2903295996014283373108181 68045999906584766557223)
                  ·
                    rfl

theorem cell23_1192672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_1192672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192672 prefixEnd_1192672 := by exact prefixLift 1192672
  have htrace : WordTrace (prefixWord ++ tailWord_1192672) baseStart_1192672 baseEnd_1192672 := by
    simpa [prefixWord, tailWord_1192672, baseEnd_1192672] using wordTrace_append hprefix tailTrace_1192672
  have hstable : (prefixWord ++ tailWord_1192672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192672).length < 2 ^ (prefixWord ++ tailWord_1192672).sum := by decide
  have hdescent : baseEnd_1192672 < baseStart_1192672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192759 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_1192759 : Nat := 118140960795 + 1192759 * 2 ^ 59
def prefixEnd_1192759 : Nat := 4983230072969 + 3 ^ 40 * 1192759 * 2
def baseEnd_1192759 : Nat := 612458671976204058627107

theorem tailTrace_1192759 : CollatzResearch.WordTrace tailWord_1192759 prefixEnd_1192759 612458671976204058627107 := by
  unfold tailWord_1192759
  simp only [CollatzResearch.WordTrace]
  refine ⟨43503494685845324864365331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29002329790563549909576887 43503494685845324864365331)
  ·
    refine ⟨65255242028767987296547997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43503494685845324864365331 65255242028767987296547997)
    ·
      refine ⟨24470715760787995236205499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65255242028767987296547997 24470715760787995236205499)
      ·
        refine ⟨36706073641181992854308249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24470715760787995236205499 36706073641181992854308249)
        ·
          refine ⟨27529555230886494640731187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36706073641181992854308249 27529555230886494640731187)
          ·
            refine ⟨41294332846329741961096781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27529555230886494640731187 41294332846329741961096781)
            ·
              refine ⟨15485374817373653235411293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41294332846329741961096781 15485374817373653235411293)
              ·
                refine ⟨5807015556515119963279235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15485374817373653235411293 5807015556515119963279235)
                ·
                  refine ⟨8710523334772679944918853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807015556515119963279235 8710523334772679944918853)
                  ·
                    refine ⟨1633223125269877489672285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8710523334772679944918853 1633223125269877489672285)
                    ·
                      refine ⟨612458671976204058627107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1633223125269877489672285 612458671976204058627107)
                      ·
                        rfl

theorem cell23_1192759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_1192759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192759 prefixEnd_1192759 := by exact prefixLift 1192759
  have htrace : WordTrace (prefixWord ++ tailWord_1192759) baseStart_1192759 baseEnd_1192759 := by
    simpa [prefixWord, tailWord_1192759, baseEnd_1192759] using wordTrace_append hprefix tailTrace_1192759
  have hstable : (prefixWord ++ tailWord_1192759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192759).length < 2 ^ (prefixWord ++ tailWord_1192759).sum := by decide
  have hdescent : baseEnd_1192759 < baseStart_1192759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192776 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_1192776 : Nat := 118140960795 + 1192776 * 2 ^ 59
def prefixEnd_1192776 : Nat := 4983230072969 + 3 ^ 40 * 1192776 * 2
def baseEnd_1192776 : Nat := 612467401147330492114529

theorem tailTrace_1192776 : CollatzResearch.WordTrace tailWord_1192776 prefixEnd_1192776 612467401147330492114529 := by
  unfold tailWord_1192776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21752057363391868383867091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29002743151189157845156121 21752057363391868383867091)
  ·
    refine ⟨32628086045087802575800637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21752057363391868383867091 32628086045087802575800637)
    ·
      refine ⟨12235532266907925965925239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32628086045087802575800637 12235532266907925965925239)
      ·
        refine ⟨18353298400361888948887859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12235532266907925965925239 18353298400361888948887859)
        ·
          refine ⟨27529947600542833423331789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18353298400361888948887859 27529947600542833423331789)
          ·
            refine ⟨10323730350203562533749421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27529947600542833423331789 10323730350203562533749421)
            ·
              refine ⟨3871398881326335950156033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10323730350203562533749421 3871398881326335950156033)
              ·
                refine ⟨2903549160994751962617025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871398881326335950156033 2903549160994751962617025)
                ·
                  refine ⟨2177661870746063971962769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903549160994751962617025 2177661870746063971962769)
                  ·
                    refine ⟨1633246403059547978972077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2177661870746063971962769 1633246403059547978972077)
                    ·
                      refine ⟨612467401147330492114529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1633246403059547978972077 612467401147330492114529)
                      ·
                        rfl

theorem cell23_1192776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_1192776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192776 prefixEnd_1192776 := by exact prefixLift 1192776
  have htrace : WordTrace (prefixWord ++ tailWord_1192776) baseStart_1192776 baseEnd_1192776 := by
    simpa [prefixWord, tailWord_1192776, baseEnd_1192776] using wordTrace_append hprefix tailTrace_1192776
  have hstable : (prefixWord ++ tailWord_1192776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192776).length < 2 ^ (prefixWord ++ tailWord_1192776).sum := by decide
  have hdescent : baseEnd_1192776 < baseStart_1192776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192816 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2]
def baseStart_1192816 : Nat := 118140960795 + 1192816 * 2 ^ 59
def prefixEnd_1192816 : Nat := 4983230072969 + 3 ^ 40 * 1192816 * 2
def baseEnd_1192816 : Nat := 612487940373510335614345

theorem tailTrace_1192816 : CollatzResearch.WordTrace tailWord_1192816 prefixEnd_1192816 612487940373510335614345 := by
  unfold tailWord_1192816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21752786823319411799595151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29003715764425882399460201 21752786823319411799595151)
  ·
    refine ⟨32629180234979117699392727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21752786823319411799595151 32629180234979117699392727)
    ·
      refine ⟨48943770352468676549089091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32629180234979117699392727 48943770352468676549089091)
      ·
        refine ⟨73415655528703014823633637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48943770352468676549089091 73415655528703014823633637)
        ·
          refine ⟨13765435411631815279431307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73415655528703014823633637 13765435411631815279431307)
          ·
            refine ⟨20648153117447722919146961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765435411631815279431307 20648153117447722919146961)
            ·
              refine ⟨15486114838085792189360221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20648153117447722919146961 15486114838085792189360221)
              ·
                refine ⟨5807293064282172071010083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15486114838085792189360221 5807293064282172071010083)
                ·
                  refine ⟨8710939596423258106515125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807293064282172071010083 8710939596423258106515125)
                  ·
                    refine ⟨816650587164680447485793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8710939596423258106515125 816650587164680447485793)
                    ·
                      refine ⟨612487940373510335614345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816650587164680447485793 612487940373510335614345)
                      ·
                        rfl

theorem cell23_1192816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2].length) (baseStart_1192816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192816 prefixEnd_1192816 := by exact prefixLift 1192816
  have htrace : WordTrace (prefixWord ++ tailWord_1192816) baseStart_1192816 baseEnd_1192816 := by
    simpa [prefixWord, tailWord_1192816, baseEnd_1192816] using wordTrace_append hprefix tailTrace_1192816
  have hstable : (prefixWord ++ tailWord_1192816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192816).length < 2 ^ (prefixWord ++ tailWord_1192816).sum := by decide
  have hdescent : baseEnd_1192816 < baseStart_1192816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192830 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1192830 : Nat := 118140960795 + 1192830 * 2 ^ 59
def prefixEnd_1192830 : Nat := 4983230072969 + 3 ^ 40 * 1192830 * 2
def baseEnd_1192830 : Nat := 68055014344741475648809

theorem tailTrace_1192830 : CollatzResearch.WordTrace tailWord_1192830 prefixEnd_1192830 68055014344741475648809 := by
  unfold tailWord_1192830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438260533573512998774993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29004056179058735993466629 5438260533573512998774993)
  ·
    refine ⟨4078695400180134749081245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5438260533573512998774993 4078695400180134749081245)
    ·
      refine ⟨1529510775067550530905467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4078695400180134749081245 1529510775067550530905467)
      ·
        refine ⟨2294266162601325796358201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529510775067550530905467 2294266162601325796358201)
        ·
          refine ⟨1720699621950994347268651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2294266162601325796358201 1720699621950994347268651)
          ·
            refine ⟨2581049432926491520902977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720699621950994347268651 2581049432926491520902977)
            ·
              refine ⟨1935787074694868640677233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581049432926491520902977 1935787074694868640677233)
              ·
                refine ⟨1451840306021151480507925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935787074694868640677233 1451840306021151480507925)
                ·
                  refine ⟨68055014344741475648809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1451840306021151480507925 68055014344741475648809)
                  ·
                    rfl

theorem cell23_1192830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1192830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192830 prefixEnd_1192830 := by exact prefixLift 1192830
  have htrace : WordTrace (prefixWord ++ tailWord_1192830) baseStart_1192830 baseEnd_1192830 := by
    simpa [prefixWord, tailWord_1192830, baseEnd_1192830] using wordTrace_append hprefix tailTrace_1192830
  have hstable : (prefixWord ++ tailWord_1192830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192830).length < 2 ^ (prefixWord ++ tailWord_1192830).sum := by decide
  have hdescent : baseEnd_1192830 < baseStart_1192830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192834 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1192834 : Nat := 118140960795 + 1192834 * 2 ^ 59
def prefixEnd_1192834 : Nat := 4983230072969 + 3 ^ 40 * 1192834 * 2
def baseEnd_1192834 : Nat := 204165727675097088396421

theorem tailTrace_1192834 : CollatzResearch.WordTrace tailWord_1192834 prefixEnd_1192834 204165727675097088396421 := by
  unfold tailWord_1192834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876557540143403168336389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29004153440382408448897037 10876557540143403168336389)
  ·
    refine ⟨2039354538776888094063073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10876557540143403168336389 2039354538776888094063073)
    ·
      refine ⟨1529515904082666070547305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2039354538776888094063073 1529515904082666070547305)
      ·
        refine ⟨1147136928061999552910479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529515904082666070547305 1147136928061999552910479)
        ·
          refine ⟨1720705392092999329365719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147136928061999552910479 1720705392092999329365719)
          ·
            refine ⟨2581058088139498994048579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720705392092999329365719 2581058088139498994048579)
            ·
              refine ⟨3871587132209248491072869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581058088139498994048579 3871587132209248491072869)
              ·
                refine ⟨725922587289234092076163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3871587132209248491072869 725922587289234092076163)
                ·
                  refine ⟨1088883880933851138114245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725922587289234092076163 1088883880933851138114245)
                  ·
                    refine ⟨204165727675097088396421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1088883880933851138114245 204165727675097088396421)
                    ·
                      rfl

theorem cell23_1192834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1192834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192834 prefixEnd_1192834 := by exact prefixLift 1192834
  have htrace : WordTrace (prefixWord ++ tailWord_1192834) baseStart_1192834 baseEnd_1192834 := by
    simpa [prefixWord, tailWord_1192834, baseEnd_1192834] using wordTrace_append hprefix tailTrace_1192834
  have hstable : (prefixWord ++ tailWord_1192834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192834).length < 2 ^ (prefixWord ++ tailWord_1192834).sum := by decide
  have hdescent : baseEnd_1192834 < baseStart_1192834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192849 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_1192849 : Nat := 118140960795 + 1192849 * 2 ^ 59
def prefixEnd_1192849 : Nat := 4983230072969 + 3 ^ 40 * 1192849 * 2
def baseEnd_1192849 : Nat := 612504885235108706501693

theorem tailTrace_1192849 : CollatzResearch.WordTrace tailWord_1192849 prefixEnd_1192849 612504885235108706501693 := by
  unfold tailWord_1192849
  simp only [CollatzResearch.WordTrace]
  refine ⟨43506777255519270235141601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29004518170346180156761067 43506777255519270235141601)
  ·
    refine ⟨32630082941639452676356201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43506777255519270235141601 32630082941639452676356201)
    ·
      refine ⟨24472562206229589507267151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32630082941639452676356201 24472562206229589507267151)
      ·
        refine ⟨36708843309344384260900727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24472562206229589507267151 36708843309344384260900727)
        ·
          refine ⟨55063264964016576391351091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36708843309344384260900727 55063264964016576391351091)
          ·
            refine ⟨82594897446024864587026637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55063264964016576391351091 82594897446024864587026637)
            ·
              refine ⟨30973086542259324220134989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82594897446024864587026637 30973086542259324220134989)
              ·
                refine ⟨11614907453347246582550621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30973086542259324220134989 11614907453347246582550621)
                ·
                  refine ⟨4355590295005217468456483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11614907453347246582550621 4355590295005217468456483)
                  ·
                    refine ⟨6533385442507826202684725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4355590295005217468456483 6533385442507826202684725)
                    ·
                      refine ⟨612504885235108706501693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6533385442507826202684725 612504885235108706501693)
                      ·
                        rfl

theorem cell23_1192849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_1192849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192849 prefixEnd_1192849 := by exact prefixLift 1192849
  have htrace : WordTrace (prefixWord ++ tailWord_1192849) baseStart_1192849 baseEnd_1192849 := by
    simpa [prefixWord, tailWord_1192849, baseEnd_1192849] using wordTrace_append hprefix tailTrace_1192849
  have hstable : (prefixWord ++ tailWord_1192849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192849).length < 2 ^ (prefixWord ++ tailWord_1192849).sum := by decide
  have hdescent : baseEnd_1192849 < baseStart_1192849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192900 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1192900 : Nat := 118140960795 + 1192900 * 2 ^ 59
def prefixEnd_1192900 : Nat := 4983230072969 + 3 ^ 40 * 1192900 * 2
def baseEnd_1192900 : Nat := 612531072748488006963959

theorem tailTrace_1192900 : CollatzResearch.WordTrace tailWord_1192900 prefixEnd_1192900 612531072748488006963959 := by
  unfold tailWord_1192900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21754318689167252972624077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29005758252223003963498769 21754318689167252972624077)
  ·
    refine ⟨8157869508437719864734029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21754318689167252972624077 8157869508437719864734029)
    ·
      refine ⟨3059201065664144949275261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8157869508437719864734029 3059201065664144949275261)
      ·
        refine ⟨1147200399624054355978223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3059201065664144949275261 1147200399624054355978223)
        ·
          refine ⟨1720800599436081533967335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147200399624054355978223 1720800599436081533967335)
          ·
            refine ⟨2581200899154122300951003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720800599436081533967335 2581200899154122300951003)
            ·
              refine ⟨3871801348731183451426505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581200899154122300951003 3871801348731183451426505)
              ·
                refine ⟨2903851011548387588569879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871801348731183451426505 2903851011548387588569879)
                ·
                  refine ⟨4355776517322581382854819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903851011548387588569879 4355776517322581382854819)
                  ·
                    refine ⟨6533664775983872074282229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4355776517322581382854819 6533664775983872074282229)
                    ·
                      refine ⟨612531072748488006963959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6533664775983872074282229 612531072748488006963959)
                      ·
                        rfl

theorem cell23_1192900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1192900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192900 prefixEnd_1192900 := by exact prefixLift 1192900
  have htrace : WordTrace (prefixWord ++ tailWord_1192900) baseStart_1192900 baseEnd_1192900 := by
    simpa [prefixWord, tailWord_1192900, baseEnd_1192900] using wordTrace_append hprefix tailTrace_1192900
  have hstable : (prefixWord ++ tailWord_1192900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192900).length < 2 ^ (prefixWord ++ tailWord_1192900).sum := by decide
  have hdescent : baseEnd_1192900 < baseStart_1192900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192919 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1192919 : Nat := 118140960795 + 1192919 * 2 ^ 59
def prefixEnd_1192919 : Nat := 4983230072969 + 3 ^ 40 * 1192919 * 2
def baseEnd_1192919 : Nat := 612540828880923432626371

theorem tailTrace_1192919 : CollatzResearch.WordTrace tailWord_1192919 prefixEnd_1192919 612540828880923432626371 := by
  unfold tailWord_1192919
  simp only [CollatzResearch.WordTrace]
  refine ⟨43509330365265672190189811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29006220243510448126793207 43509330365265672190189811)
  ·
    refine ⟨65263995547898508285284717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43509330365265672190189811 65263995547898508285284717)
    ·
      refine ⟨24473998330461940606981769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65263995547898508285284717 24473998330461940606981769)
      ·
        refine ⟨18355498747846455455236327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24473998330461940606981769 18355498747846455455236327)
        ·
          refine ⟨27533248121769683182854491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18355498747846455455236327 27533248121769683182854491)
          ·
            refine ⟨41299872182654524774281737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27533248121769683182854491 41299872182654524774281737)
            ·
              refine ⟨30974904136990893580711303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41299872182654524774281737 30974904136990893580711303)
              ·
                refine ⟨46462356205486340371066955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30974904136990893580711303 46462356205486340371066955)
                ·
                  refine ⟨69693534308229510556600433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46462356205486340371066955 69693534308229510556600433)
                  ·
                    refine ⟨52270150731172132917450325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69693534308229510556600433 52270150731172132917450325)
                    ·
                      refine ⟨612540828880923432626371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52270150731172132917450325 612540828880923432626371)
                      ·
                        rfl

theorem cell23_1192919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1192919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1192919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1192919 prefixEnd_1192919 := by exact prefixLift 1192919
  have htrace : WordTrace (prefixWord ++ tailWord_1192919) baseStart_1192919 baseEnd_1192919 := by
    simpa [prefixWord, tailWord_1192919, baseEnd_1192919] using wordTrace_append hprefix tailTrace_1192919
  have hstable : (prefixWord ++ tailWord_1192919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192919).length < 2 ^ (prefixWord ++ tailWord_1192919).sum := by decide
  have hdescent : baseEnd_1192919 < baseStart_1192919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193043 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 4, 4, 2]
def baseStart_1193043 : Nat := 118140960795 + 1193043 * 2 ^ 59
def prefixEnd_1193043 : Nat := 4983230072969 + 3 ^ 40 * 1193043 * 2
def baseEnd_1193043 : Nat := 612604500482080947475801

theorem tailTrace_1193043 : CollatzResearch.WordTrace tailWord_1193043 prefixEnd_1193043 612604500482080947475801 := by
  unfold tailWord_1193043
  simp only [CollatzResearch.WordTrace]
  refine ⟨43513853016816441367703783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29009235344544294245135855 43513853016816441367703783)
  ·
    refine ⟨65270779525224662051555675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43513853016816441367703783 65270779525224662051555675)
    ·
      refine ⟨97906169287836993077333513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65270779525224662051555675 97906169287836993077333513)
      ·
        refine ⟨73429626965877744808000135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97906169287836993077333513 73429626965877744808000135)
        ·
          refine ⟨110144440448816617212000203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73429626965877744808000135 110144440448816617212000203)
          ·
            refine ⟨165216660673224925818000305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110144440448816617212000203 165216660673224925818000305)
            ·
              refine ⟨123912495504918694363500229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165216660673224925818000305 123912495504918694363500229)
              ·
                refine ⟨23233592907172255193156293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123912495504918694363500229 23233592907172255193156293)
                ·
                  refine ⟨4356298670094797848716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23233592907172255193156293 4356298670094797848716805)
                  ·
                    refine ⟨816806000642774596634401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356298670094797848716805 816806000642774596634401)
                    ·
                      refine ⟨612604500482080947475801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816806000642774596634401 612604500482080947475801)
                      ·
                        rfl

theorem cell23_1193043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4, 2].length) (baseStart_1193043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193043 prefixEnd_1193043 := by exact prefixLift 1193043
  have htrace : WordTrace (prefixWord ++ tailWord_1193043) baseStart_1193043 baseEnd_1193043 := by
    simpa [prefixWord, tailWord_1193043, baseEnd_1193043] using wordTrace_append hprefix tailTrace_1193043
  have hstable : (prefixWord ++ tailWord_1193043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193043).length < 2 ^ (prefixWord ++ tailWord_1193043).sum := by decide
  have hdescent : baseEnd_1193043 < baseStart_1193043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193056 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1193056 : Nat := 118140960795 + 1193056 * 2 ^ 59
def prefixEnd_1193056 : Nat := 4983230072969 + 3 ^ 40 * 1193056 * 2
def baseEnd_1193056 : Nat := 612611175730589396613241

theorem tailTrace_1193056 : CollatzResearch.WordTrace tailWord_1193056 prefixEnd_1193056 612611175730589396613241 := by
  unfold tailWord_1193056
  simp only [CollatzResearch.WordTrace]
  refine ⟨21757163582884672293963511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29009551443846229725284681 21757163582884672293963511)
  ·
    refine ⟨32635745374327008440945267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21757163582884672293963511 32635745374327008440945267)
    ·
      refine ⟨48953618061490512661417901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32635745374327008440945267 48953618061490512661417901)
      ·
        refine ⟨18357606773058942248031713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48953618061490512661417901 18357606773058942248031713)
        ·
          refine ⟨13768205079794206686023785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18357606773058942248031713 13768205079794206686023785)
          ·
            refine ⟨10326153809845655014517839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13768205079794206686023785 10326153809845655014517839)
            ·
              refine ⟨15489230714768482521776759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326153809845655014517839 15489230714768482521776759)
              ·
                refine ⟨23233846072152723782665139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15489230714768482521776759 23233846072152723782665139)
                ·
                  refine ⟨34850769108229085673997709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23233846072152723782665139 34850769108229085673997709)
                  ·
                    refine ⟨13069038415585907127749141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34850769108229085673997709 13069038415585907127749141)
                    ·
                      refine ⟨612611175730589396613241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13069038415585907127749141 612611175730589396613241)
                      ·
                        rfl

theorem cell23_1193056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1193056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193056 prefixEnd_1193056 := by exact prefixLift 1193056
  have htrace : WordTrace (prefixWord ++ tailWord_1193056) baseStart_1193056 baseEnd_1193056 := by
    simpa [prefixWord, tailWord_1193056, baseEnd_1193056] using wordTrace_append hprefix tailTrace_1193056
  have hstable : (prefixWord ++ tailWord_1193056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193056).length < 2 ^ (prefixWord ++ tailWord_1193056).sum := by decide
  have hdescent : baseEnd_1193056 < baseStart_1193056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193070 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1193070 : Nat := 118140960795 + 1193070 * 2 ^ 59
def prefixEnd_1193070 : Nat := 4983230072969 + 3 ^ 40 * 1193070 * 2
def baseEnd_1193070 : Nat := 204206121486584113946059

theorem tailTrace_1193070 : CollatzResearch.WordTrace tailWord_1193070 prefixEnd_1193070 204206121486584113946059 := by
  unfold tailWord_1193070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439354723464828122367083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29009891858479083319291109 5439354723464828122367083)
  ·
    refine ⟨8159032085197242183550625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439354723464828122367083 8159032085197242183550625)
    ·
      refine ⟨6119274063897931637662969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8159032085197242183550625 6119274063897931637662969)
      ·
        refine ⟨4589455547923448728247227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119274063897931637662969 4589455547923448728247227)
        ·
          refine ⟨6884183321885173092370841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589455547923448728247227 6884183321885173092370841)
          ·
            refine ⟨5163137491413879819278131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6884183321885173092370841 5163137491413879819278131)
            ·
              refine ⟨7744706237120819728917197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163137491413879819278131 7744706237120819728917197)
              ·
                refine ⟨2904264838920307398343949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7744706237120819728917197 2904264838920307398343949)
                ·
                  refine ⟨1089099314595115274378981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2904264838920307398343949 1089099314595115274378981)
                  ·
                    refine ⟨204206121486584113946059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089099314595115274378981 204206121486584113946059)
                    ·
                      rfl

theorem cell23_1193070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1193070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193070 prefixEnd_1193070 := by exact prefixLift 1193070
  have htrace : WordTrace (prefixWord ++ tailWord_1193070) baseStart_1193070 baseEnd_1193070 := by
    simpa [prefixWord, tailWord_1193070, baseEnd_1193070] using wordTrace_append hprefix tailTrace_1193070
  have hstable : (prefixWord ++ tailWord_1193070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193070).length < 2 ^ (prefixWord ++ tailWord_1193070).sum := by decide
  have hdescent : baseEnd_1193070 < baseStart_1193070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193143 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 1, 6]
def baseStart_1193143 : Nat := 118140960795 + 1193143 * 2 ^ 59
def prefixEnd_1193143 : Nat := 4983230072969 + 3 ^ 40 * 1193143 * 2
def baseEnd_1193143 : Nat := 204218616182510185408447

theorem tailTrace_1193143 : CollatzResearch.WordTrace tailWord_1193143 prefixEnd_1193143 204218616182510185408447 := by
  unfold tailWord_1193143
  simp only [CollatzResearch.WordTrace]
  refine ⟨43517500316454158446344083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29011666877636105630896055 43517500316454158446344083)
  ·
    refine ⟨65276250474681237669516125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43517500316454158446344083 65276250474681237669516125)
    ·
      refine ⟨24478593928005464126068547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65276250474681237669516125 24478593928005464126068547)
      ·
        refine ⟨36717890892008196189102821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24478593928005464126068547 36717890892008196189102821)
        ·
          refine ⟨6884604542251536785456779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36717890892008196189102821 6884604542251536785456779)
          ·
            refine ⟨10326906813377305178185169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884604542251536785456779 10326906813377305178185169)
            ·
              refine ⟨7745180110032978883638877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10326906813377305178185169 7745180110032978883638877)
              ·
                refine ⟨2904442541262367081364579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7745180110032978883638877 2904442541262367081364579)
                ·
                  refine ⟨4356663811893550622046869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904442541262367081364579 4356663811893550622046869)
                  ·
                    refine ⟨204218616182510185408447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4356663811893550622046869 204218616182510185408447)
                    ·
                      rfl

theorem cell23_1193143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_1193143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193143 prefixEnd_1193143 := by exact prefixLift 1193143
  have htrace : WordTrace (prefixWord ++ tailWord_1193143) baseStart_1193143 baseEnd_1193143 := by
    simpa [prefixWord, tailWord_1193143, baseEnd_1193143] using wordTrace_append hprefix tailTrace_1193143
  have hstable : (prefixWord ++ tailWord_1193143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193143).length < 2 ^ (prefixWord ++ tailWord_1193143).sum := by decide
  have hdescent : baseEnd_1193143 < baseStart_1193143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193173 : List Nat := [1, 3, 2, 4, 1, 12]
def baseStart_1193173 : Nat := 118140960795 + 1193173 * 2 ^ 59
def prefixEnd_1193173 : Nat := 4983230072969 + 3 ^ 40 * 1193173 * 2
def baseEnd_1193173 : Nat := 2521280876408088225721

theorem tailTrace_1193173 : CollatzResearch.WordTrace tailWord_1193173 prefixEnd_1193173 2521280876408088225721 := by
  unfold tailWord_1193173
  simp only [CollatzResearch.WordTrace]
  refine ⟨43518594506345473569936173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29012396337563649046624115 43518594506345473569936173)
  ·
    refine ⟨16319472939879552588726065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43518594506345473569936173 16319472939879552588726065)
    ·
      refine ⟨12239604704909664441544549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16319472939879552588726065 12239604704909664441544549)
      ·
        refine ⟨2294925882170562082789603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12239604704909664441544549 2294925882170562082789603)
        ·
          refine ⟨3442388823255843124184405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294925882170562082789603 3442388823255843124184405)
          ·
            refine ⟨2521280876408088225721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3442388823255843124184405 2521280876408088225721)
            ·
              rfl

theorem cell23_1193173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 12].length) (baseStart_1193173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193173 prefixEnd_1193173 := by exact prefixLift 1193173
  have htrace : WordTrace (prefixWord ++ tailWord_1193173) baseStart_1193173 baseEnd_1193173 := by
    simpa [prefixWord, tailWord_1193173, baseEnd_1193173] using wordTrace_append hprefix tailTrace_1193173
  have hstable : (prefixWord ++ tailWord_1193173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193173).length < 2 ^ (prefixWord ++ tailWord_1193173).sum := by decide
  have hdescent : baseEnd_1193173 < baseStart_1193173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193197 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1193197 : Nat := 118140960795 + 1193197 * 2 ^ 59
def prefixEnd_1193197 : Nat := 4983230072969 + 3 ^ 40 * 1193197 * 2
def baseEnd_1193197 : Nat := 612683576502873344950093

theorem tailTrace_1193197 : CollatzResearch.WordTrace tailWord_1193197 prefixEnd_1193197 612683576502873344950093 := by
  unfold tailWord_1193197
  simp only [CollatzResearch.WordTrace]
  refine ⟨43519469858258525668809845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29012979905505683779206563 43519469858258525668809845)
  ·
    refine ⟨4079950299211736781450923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43519469858258525668809845 4079950299211736781450923)
    ·
      refine ⟨6119925448817605172176385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079950299211736781450923 6119925448817605172176385)
      ·
        refine ⟨4589944086613203879132289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119925448817605172176385 4589944086613203879132289)
        ·
          refine ⟨3442458064959902909349217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589944086613203879132289 3442458064959902909349217)
          ·
            refine ⟨2581843548719927182011913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442458064959902909349217 2581843548719927182011913)
            ·
              refine ⟨1936382661539945386508935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581843548719927182011913 1936382661539945386508935)
              ·
                refine ⟨2904573992309918079763403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936382661539945386508935 2904573992309918079763403)
                ·
                  refine ⟨4356860988464877119645105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904573992309918079763403 4356860988464877119645105)
                  ·
                    refine ⟨3267645741348657839733829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4356860988464877119645105 3267645741348657839733829)
                    ·
                      refine ⟨612683576502873344950093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3267645741348657839733829 612683576502873344950093)
                      ·
                        rfl

theorem cell23_1193197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1193197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193197 prefixEnd_1193197 := by exact prefixLift 1193197
  have htrace : WordTrace (prefixWord ++ tailWord_1193197) baseStart_1193197 baseEnd_1193197 := by
    simpa [prefixWord, tailWord_1193197, baseEnd_1193197] using wordTrace_append hprefix tailTrace_1193197
  have hstable : (prefixWord ++ tailWord_1193197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193197).length < 2 ^ (prefixWord ++ tailWord_1193197).sum := by decide
  have hdescent : baseEnd_1193197 < baseStart_1193197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193200 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3]
def baseStart_1193200 : Nat := 118140960795 + 1193200 * 2 ^ 59
def prefixEnd_1193200 : Nat := 4983230072969 + 3 ^ 40 * 1193200 * 2
def baseEnd_1193200 : Nat := 612685116944836833212579

theorem tailTrace_1193200 : CollatzResearch.WordTrace tailWord_1193200 prefixEnd_1193200 612685116944836833212579 := by
  unfold tailWord_1193200
  simp only [CollatzResearch.WordTrace]
  refine ⟨21759789638623828590584527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29013052851498438120779369 21759789638623828590584527)
  ·
    refine ⟨32639684457935742885876791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21759789638623828590584527 32639684457935742885876791)
    ·
      refine ⟨48959526686903614328815187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32639684457935742885876791 48959526686903614328815187)
      ·
        refine ⟨73439290030355421493222781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48959526686903614328815187 73439290030355421493222781)
        ·
          refine ⟨27539733761383283059958543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73439290030355421493222781 27539733761383283059958543)
          ·
            refine ⟨41309600642074924589937815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27539733761383283059958543 41309600642074924589937815)
            ·
              refine ⟨61964400963112386884906723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41309600642074924589937815 61964400963112386884906723)
              ·
                refine ⟨92946601444668580327360085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61964400963112386884906723 92946601444668580327360085)
                ·
                  refine ⟨1089217985679709925711251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 92946601444668580327360085 1089217985679709925711251)
                  ·
                    refine ⟨1633826978519564888566877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1089217985679709925711251 1633826978519564888566877)
                    ·
                      refine ⟨612685116944836833212579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1633826978519564888566877 612685116944836833212579)
                      ·
                        rfl

theorem cell23_1193200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_1193200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193200 prefixEnd_1193200 := by exact prefixLift 1193200
  have htrace : WordTrace (prefixWord ++ tailWord_1193200) baseStart_1193200 baseEnd_1193200 := by
    simpa [prefixWord, tailWord_1193200, baseEnd_1193200] using wordTrace_append hprefix tailTrace_1193200
  have hstable : (prefixWord ++ tailWord_1193200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193200).length < 2 ^ (prefixWord ++ tailWord_1193200).sum := by decide
  have hdescent : baseEnd_1193200 < baseStart_1193200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193218 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1193218 : Nat := 118140960795 + 1193218 * 2 ^ 59
def prefixEnd_1193218 : Nat := 4983230072969 + 3 ^ 40 * 1193218 * 2
def baseEnd_1193218 : Nat := 612694359596617762787497

theorem tailTrace_1193218 : CollatzResearch.WordTrace tailWord_1193218 prefixEnd_1193218 612694359596617762787497 := by
  unfold tailWord_1193218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880058947795611563831077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29013490527454964170216205 10880058947795611563831077)
  ·
    refine ⟨2040011052711677168218327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10880058947795611563831077 2040011052711677168218327)
    ·
      refine ⟨3060016579067515752327491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040011052711677168218327 3060016579067515752327491)
      ·
        refine ⟨4590024868601273628491237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060016579067515752327491 4590024868601273628491237)
        ·
          refine ⟨860629662862738805342107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4590024868601273628491237 860629662862738805342107)
          ·
            refine ⟨1290944494294108208013161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860629662862738805342107 1290944494294108208013161)
            ·
              refine ⟨968208370720581156009871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290944494294108208013161 968208370720581156009871)
              ·
                refine ⟨1452312556080871734014807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968208370720581156009871 1452312556080871734014807)
                ·
                  refine ⟨2178468834121307601022211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452312556080871734014807 2178468834121307601022211)
                  ·
                    refine ⟨3267703251181961401533317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178468834121307601022211 3267703251181961401533317)
                    ·
                      refine ⟨612694359596617762787497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3267703251181961401533317 612694359596617762787497)
                      ·
                        rfl

theorem cell23_1193218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1193218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193218 prefixEnd_1193218 := by exact prefixLift 1193218
  have htrace : WordTrace (prefixWord ++ tailWord_1193218) baseStart_1193218 baseEnd_1193218 := by
    simpa [prefixWord, tailWord_1193218, baseEnd_1193218] using wordTrace_append hprefix tailTrace_1193218
  have hstable : (prefixWord ++ tailWord_1193218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193218).length < 2 ^ (prefixWord ++ tailWord_1193218).sum := by decide
  have hdescent : baseEnd_1193218 < baseStart_1193218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193233 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1193233 : Nat := 118140960795 + 1193233 * 2 ^ 59
def prefixEnd_1193233 : Nat := 4983230072969 + 3 ^ 40 * 1193233 * 2
def baseEnd_1193233 : Nat := 204234020602145068033309

theorem tailTrace_1193233 : CollatzResearch.WordTrace tailWord_1193233 prefixEnd_1193233 204234020602145068033309 := by
  unfold tailWord_1193233
  simp only [CollatzResearch.WordTrace]
  refine ⟨43520782886128103817120353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29013855257418735878080235 43520782886128103817120353)
  ·
    refine ⟨32640587164596077862840265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43520782886128103817120353 32640587164596077862840265)
    ·
      refine ⟨24480440373447058397130199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32640587164596077862840265 24480440373447058397130199)
      ·
        refine ⟨36720660560170587595695299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24480440373447058397130199 36720660560170587595695299)
        ·
          refine ⟨55080990840255881393542949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36720660560170587595695299 55080990840255881393542949)
          ·
            refine ⟨10327685782547977761289303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55080990840255881393542949 10327685782547977761289303)
            ·
              refine ⟨15491528673821966641933955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327685782547977761289303 15491528673821966641933955)
              ·
                refine ⟨23237293010732949962900933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15491528673821966641933955 23237293010732949962900933)
                ·
                  refine ⟨4356992439512428118043925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23237293010732949962900933 4356992439512428118043925)
                  ·
                    refine ⟨204234020602145068033309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4356992439512428118043925 204234020602145068033309)
                    ·
                      rfl

theorem cell23_1193233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1193233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193233 prefixEnd_1193233 := by exact prefixLift 1193233
  have htrace : WordTrace (prefixWord ++ tailWord_1193233) baseStart_1193233 baseEnd_1193233 := by
    simpa [prefixWord, tailWord_1193233, baseEnd_1193233] using wordTrace_append hprefix tailTrace_1193233
  have hstable : (prefixWord ++ tailWord_1193233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193233).length < 2 ^ (prefixWord ++ tailWord_1193233).sum := by decide
  have hdescent : baseEnd_1193233 < baseStart_1193233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193243 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_1193243 : Nat := 118140960795 + 1193243 * 2 ^ 59
def prefixEnd_1193243 : Nat := 4983230072969 + 3 ^ 40 * 1193243 * 2
def baseEnd_1193243 : Nat := 612707196612980164974881

theorem tailTrace_1193243 : CollatzResearch.WordTrace tailWord_1193243 prefixEnd_1193243 612707196612980164974881 := by
  unfold tailWord_1193243
  simp only [CollatzResearch.WordTrace]
  refine ⟨43521147616091875524984383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29014098410727917016656255 43521147616091875524984383)
  ·
    refine ⟨65281721424137813287476575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43521147616091875524984383 65281721424137813287476575)
    ·
      refine ⟨97922582136206719931214863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65281721424137813287476575 97922582136206719931214863)
      ·
        refine ⟨146883873204310079896822295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97922582136206719931214863 146883873204310079896822295)
        ·
          refine ⟨220325809806465119845233443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146883873204310079896822295 220325809806465119845233443)
          ·
            refine ⟨330488714709697679767850165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220325809806465119845233443 330488714709697679767850165)
            ·
              refine ⟨30983317004034157478235953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 330488714709697679767850165 30983317004034157478235953)
              ·
                refine ⟨23237487753025618108676965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30983317004034157478235953 23237487753025618108676965)
                ·
                  refine ⟨4357028953692303395376931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23237487753025618108676965 4357028953692303395376931)
                  ·
                    refine ⟨6535543430538455093065397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357028953692303395376931 6535543430538455093065397)
                    ·
                      refine ⟨612707196612980164974881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6535543430538455093065397 612707196612980164974881)
                      ·
                        rfl

theorem cell23_1193243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_1193243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193243 prefixEnd_1193243 := by exact prefixLift 1193243
  have htrace : WordTrace (prefixWord ++ tailWord_1193243) baseStart_1193243 baseEnd_1193243 := by
    simpa [prefixWord, tailWord_1193243, baseEnd_1193243] using wordTrace_append hprefix tailTrace_1193243
  have hstable : (prefixWord ++ tailWord_1193243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193243).length < 2 ^ (prefixWord ++ tailWord_1193243).sum := by decide
  have hdescent : baseEnd_1193243 < baseStart_1193243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193261 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1193261 : Nat := 118140960795 + 1193261 * 2 ^ 59
def prefixEnd_1193261 : Nat := 4983230072969 + 3 ^ 40 * 1193261 * 2
def baseEnd_1193261 : Nat := 612716439264761094549799

theorem tailTrace_1193261 : CollatzResearch.WordTrace tailWord_1193261 prefixEnd_1193261 612716439264761094549799 := by
  unfold tailWord_1193261
  simp only [CollatzResearch.WordTrace]
  refine ⟨43521804130026664599139637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29014536086684443066093091 43521804130026664599139637)
  ·
    refine ⟨4080169137189999806169341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43521804130026664599139637 4080169137189999806169341)
    ·
      refine ⟨1530063426446249927313503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4080169137189999806169341 1530063426446249927313503)
      ·
        refine ⟨2295095139669374890970255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530063426446249927313503 2295095139669374890970255)
        ·
          refine ⟨3442642709504062336455383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295095139669374890970255 3442642709504062336455383)
          ·
            refine ⟨5163964064256093504683075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442642709504062336455383 5163964064256093504683075)
            ·
              refine ⟨7745946096384140257024613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163964064256093504683075 7745946096384140257024613)
              ·
                refine ⟨1452364893072026298192115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7745946096384140257024613 1452364893072026298192115)
                ·
                  refine ⟨2178547339608039447288173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452364893072026298192115 2178547339608039447288173)
                  ·
                    refine ⟨816955252353014792733065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178547339608039447288173 816955252353014792733065)
                    ·
                      refine ⟨612716439264761094549799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 816955252353014792733065 612716439264761094549799)
                      ·
                        rfl

theorem cell23_1193261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1193261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193261 prefixEnd_1193261 := by exact prefixLift 1193261
  have htrace : WordTrace (prefixWord ++ tailWord_1193261) baseStart_1193261 baseEnd_1193261 := by
    simpa [prefixWord, tailWord_1193261, baseEnd_1193261] using wordTrace_append hprefix tailTrace_1193261
  have hstable : (prefixWord ++ tailWord_1193261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193261).length < 2 ^ (prefixWord ++ tailWord_1193261).sum := by decide
  have hdescent : baseEnd_1193261 < baseStart_1193261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193290 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1193290 : Nat := 118140960795 + 1193290 * 2 ^ 59
def prefixEnd_1193290 : Nat := 4983230072969 + 3 ^ 40 * 1193290 * 2
def baseEnd_1193290 : Nat := 612731330203741481087165

theorem tailTrace_1193290 : CollatzResearch.WordTrace tailWord_1193290 prefixEnd_1193290 612731330203741481087165 := by
  unfold tailWord_1193290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880715461730400637986331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29015241231281068367963549 10880715461730400637986331)
  ·
    refine ⟨16321073192595600956979497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10880715461730400637986331 16321073192595600956979497)
    ·
      refine ⟨12240804894446700717734623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16321073192595600956979497 12240804894446700717734623)
      ·
        refine ⟨18361207341670051076601935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240804894446700717734623 18361207341670051076601935)
        ·
          refine ⟨27541811012505076614902903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18361207341670051076601935 27541811012505076614902903)
          ·
            refine ⟨41312716518757614922354355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27541811012505076614902903 41312716518757614922354355)
            ·
              refine ⟨61969074778136422383531533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41312716518757614922354355 61969074778136422383531533)
              ·
                refine ⟨23238403041801158393824325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61969074778136422383531533 23238403041801158393824325)
                ·
                  refine ⟨4357200570337717198842061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23238403041801158393824325 4357200570337717198842061)
                  ·
                    refine ⟨1633950213876643949565773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4357200570337717198842061 1633950213876643949565773)
                    ·
                      refine ⟨612731330203741481087165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1633950213876643949565773 612731330203741481087165)
                      ·
                        rfl

theorem cell23_1193290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1193290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193290 prefixEnd_1193290 := by exact prefixLift 1193290
  have htrace : WordTrace (prefixWord ++ tailWord_1193290) baseStart_1193290 baseEnd_1193290 := by
    simpa [prefixWord, tailWord_1193290, baseEnd_1193290] using wordTrace_append hprefix tailTrace_1193290
  have hstable : (prefixWord ++ tailWord_1193290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193290).length < 2 ^ (prefixWord ++ tailWord_1193290).sum := by decide
  have hdescent : baseEnd_1193290 < baseStart_1193290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193347 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4]
def baseStart_1193347 : Nat := 118140960795 + 1193347 * 2 ^ 59
def prefixEnd_1193347 : Nat := 4983230072969 + 3 ^ 40 * 1193347 * 2
def baseEnd_1193347 : Nat := 612760598601047758074403

theorem tailTrace_1193347 : CollatzResearch.WordTrace tailWord_1193347 prefixEnd_1193347 612760598601047758074403 := by
  unfold tailWord_1193347
  simp only [CollatzResearch.WordTrace]
  refine ⟨43524940807715101286770295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29016627205143400857846863 43524940807715101286770295)
  ·
    refine ⟨65287411211572651930155443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43524940807715101286770295 65287411211572651930155443)
    ·
      refine ⟨97931116817358977895233165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65287411211572651930155443 97931116817358977895233165)
      ·
        refine ⟨36724168806509616710712437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97931116817358977895233165 36724168806509616710712437)
        ·
          refine ⟨3442890825610276566629291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36724168806509616710712437 3442890825610276566629291)
          ·
            refine ⟨5164336238415414849943937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442890825610276566629291 5164336238415414849943937)
            ·
              refine ⟨3873252178811561137457953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5164336238415414849943937 3873252178811561137457953)
              ·
                refine ⟨2904939134108670853093465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873252178811561137457953 2904939134108670853093465)
                ·
                  refine ⟨2178704350581503139820099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2904939134108670853093465 2178704350581503139820099)
                  ·
                    refine ⟨3268056525872254709730149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178704350581503139820099 3268056525872254709730149)
                    ·
                      refine ⟨612760598601047758074403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3268056525872254709730149 612760598601047758074403)
                      ·
                        rfl

theorem cell23_1193347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_1193347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193347 prefixEnd_1193347 := by exact prefixLift 1193347
  have htrace : WordTrace (prefixWord ++ tailWord_1193347) baseStart_1193347 baseEnd_1193347 := by
    simpa [prefixWord, tailWord_1193347, baseEnd_1193347] using wordTrace_append hprefix tailTrace_1193347
  have hstable : (prefixWord ++ tailWord_1193347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193347).length < 2 ^ (prefixWord ++ tailWord_1193347).sum := by decide
  have hdescent : baseEnd_1193347 < baseStart_1193347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193364 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1193364 : Nat := 118140960795 + 1193364 * 2 ^ 59
def prefixEnd_1193364 : Nat := 4983230072969 + 3 ^ 40 * 1193364 * 2
def baseEnd_1193364 : Nat := 612769327772174191561825

theorem tailTrace_1193364 : CollatzResearch.WordTrace tailWord_1193364 prefixEnd_1193364 612769327772174191561825 := by
  unfold tailWord_1193364
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762780424326756595069573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29017040565769008793426097 21762780424326756595069573)
  ·
    refine ⟨4080521329561266861575545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21762780424326756595069573 4080521329561266861575545)
    ·
      refine ⟨3060390997170950146181659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4080521329561266861575545 3060390997170950146181659)
      ·
        refine ⟨4590586495756425219272489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060390997170950146181659 4590586495756425219272489)
        ·
          refine ⟨3442939871817318914454367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4590586495756425219272489 3442939871817318914454367)
          ·
            refine ⟨5164409807725978371681551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442939871817318914454367 5164409807725978371681551)
            ·
              refine ⟨7746614711588967557522327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164409807725978371681551 7746614711588967557522327)
              ·
                refine ⟨11619922067383451336283491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7746614711588967557522327 11619922067383451336283491)
                ·
                  refine ⟨17429883101075177004425237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11619922067383451336283491 17429883101075177004425237)
                  ·
                    refine ⟨817025770362898922082433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17429883101075177004425237 817025770362898922082433)
                    ·
                      refine ⟨612769327772174191561825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817025770362898922082433 612769327772174191561825)
                      ·
                        rfl

theorem cell23_1193364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1193364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193364 prefixEnd_1193364 := by exact prefixLift 1193364
  have htrace : WordTrace (prefixWord ++ tailWord_1193364) baseStart_1193364 baseEnd_1193364 := by
    simpa [prefixWord, tailWord_1193364, baseEnd_1193364] using wordTrace_append hprefix tailTrace_1193364
  have hstable : (prefixWord ++ tailWord_1193364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193364).length < 2 ^ (prefixWord ++ tailWord_1193364).sum := by decide
  have hdescent : baseEnd_1193364 < baseStart_1193364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193434 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_1193434 : Nat := 118140960795 + 1193434 * 2 ^ 59
def prefixEnd_1193434 : Nat := 4983230072969 + 3 ^ 40 * 1193434 * 2
def baseEnd_1193434 : Nat := 204268423805996305895501

theorem tailTrace_1193434 : CollatzResearch.WordTrace tailWord_1193434 prefixEnd_1193434 204268423805996305895501 := by
  unfold tailWord_1193434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10882028489599978786296839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29018742638933276763458237 10882028489599978786296839)
  ·
    refine ⟨16323042734399968179445259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10882028489599978786296839 16323042734399968179445259)
    ·
      refine ⟨24484564101599952269167889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16323042734399968179445259 24484564101599952269167889)
      ·
        refine ⟨18363423076199964201875917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24484564101599952269167889 18363423076199964201875917)
        ·
          refine ⟨6886283653574986575703469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18363423076199964201875917 6886283653574986575703469)
          ·
            refine ⟨2582356370090619965888801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6886283653574986575703469 2582356370090619965888801)
            ·
              refine ⟨1936767277567964974416601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582356370090619965888801 1936767277567964974416601)
              ·
                refine ⟨1452575458175973730812451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936767277567964974416601 1452575458175973730812451)
                ·
                  refine ⟨2178863187263960596218677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452575458175973730812451 2178863187263960596218677)
                  ·
                    refine ⟨204268423805996305895501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2178863187263960596218677 204268423805996305895501)
                    ·
                      rfl

theorem cell23_1193434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_1193434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193434 prefixEnd_1193434 := by exact prefixLift 1193434
  have htrace : WordTrace (prefixWord ++ tailWord_1193434) baseStart_1193434 baseEnd_1193434 := by
    simpa [prefixWord, tailWord_1193434, baseEnd_1193434] using wordTrace_append hprefix tailTrace_1193434
  have hstable : (prefixWord ++ tailWord_1193434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193434).length < 2 ^ (prefixWord ++ tailWord_1193434).sum := by decide
  have hdescent : baseEnd_1193434 < baseStart_1193434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193454 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1193454 : Nat := 118140960795 + 1193454 * 2 ^ 59
def prefixEnd_1193454 : Nat := 4983230072969 + 3 ^ 40 * 1193454 * 2
def baseEnd_1193454 : Nat := 612815541031078839436411

theorem tailTrace_1193454 : CollatzResearch.WordTrace tailWord_1193454 prefixEnd_1193454 612815541031078839436411 := by
  unfold tailWord_1193454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441105427290932320114427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29019228945551639040610277 5441105427290932320114427)
  ·
    refine ⟨8161658140936398480171641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441105427290932320114427 8161658140936398480171641)
    ·
      refine ⟨6121243605702298860128731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8161658140936398480171641 6121243605702298860128731)
      ·
        refine ⟨9181865408553448290193097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6121243605702298860128731 9181865408553448290193097)
        ·
          refine ⟨6886399056415086217644823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9181865408553448290193097 6886399056415086217644823)
          ·
            refine ⟨10329598584622629326467235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886399056415086217644823 10329598584622629326467235)
            ·
              refine ⟨15494397876933943989700853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10329598584622629326467235 15494397876933943989700853)
              ·
                refine ⟨1452599800962557249034455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15494397876933943989700853 1452599800962557249034455)
                ·
                  refine ⟨2178899701443835873551683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452599800962557249034455 2178899701443835873551683)
                  ·
                    refine ⟨3268349552165753810327525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2178899701443835873551683 3268349552165753810327525)
                    ·
                      refine ⟨612815541031078839436411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3268349552165753810327525 612815541031078839436411)
                      ·
                        rfl

theorem cell23_1193454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1193454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193454 prefixEnd_1193454 := by exact prefixLift 1193454
  have htrace : WordTrace (prefixWord ++ tailWord_1193454) baseStart_1193454 baseEnd_1193454 := by
    simpa [prefixWord, tailWord_1193454, baseEnd_1193454] using wordTrace_append hprefix tailTrace_1193454
  have hstable : (prefixWord ++ tailWord_1193454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193454).length < 2 ^ (prefixWord ++ tailWord_1193454).sum := by decide
  have hdescent : baseEnd_1193454 < baseStart_1193454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193457 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_1193457 : Nat := 118140960795 + 1193457 * 2 ^ 59
def prefixEnd_1193457 : Nat := 4983230072969 + 3 ^ 40 * 1193457 * 2
def baseEnd_1193457 : Nat := 612817081473042327698897

theorem tailTrace_1193457 : CollatzResearch.WordTrace tailWord_1193457 prefixEnd_1193457 612817081473042327698897 := by
  unfold tailWord_1193457
  simp only [CollatzResearch.WordTrace]
  refine ⟨43528952837316590073274625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29019301891544393382183083 43528952837316590073274625)
  ·
    refine ⟨32646714627987442554955969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43528952837316590073274625 32646714627987442554955969)
    ·
      refine ⟨24485035970990581916216977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32646714627987442554955969 24485035970990581916216977)
      ·
        refine ⟨18363776978242936437162733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24485035970990581916216977 18363776978242936437162733)
        ·
          refine ⟨6886416366841101163936025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18363776978242936437162733 6886416366841101163936025)
          ·
            refine ⟨5164812275130825872952019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6886416366841101163936025 5164812275130825872952019)
            ·
              refine ⟨7747218412696238809428029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5164812275130825872952019 7747218412696238809428029)
              ·
                refine ⟨2905206904761089553535511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7747218412696238809428029 2905206904761089553535511)
                ·
                  refine ⟨4357810357141634330303267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905206904761089553535511 4357810357141634330303267)
                  ·
                    refine ⟨6536715535712451495454901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4357810357141634330303267 6536715535712451495454901)
                    ·
                      refine ⟨612817081473042327698897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6536715535712451495454901 612817081473042327698897)
                      ·
                        rfl

theorem cell23_1193457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_1193457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193457 prefixEnd_1193457 := by exact prefixLift 1193457
  have htrace : WordTrace (prefixWord ++ tailWord_1193457) baseStart_1193457 baseEnd_1193457 := by
    simpa [prefixWord, tailWord_1193457, baseEnd_1193457] using wordTrace_append hprefix tailTrace_1193457
  have hstable : (prefixWord ++ tailWord_1193457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193457).length < 2 ^ (prefixWord ++ tailWord_1193457).sum := by decide
  have hdescent : baseEnd_1193457 < baseStart_1193457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193485 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1193485 : Nat := 118140960795 + 1193485 * 2 ^ 59
def prefixEnd_1193485 : Nat := 4983230072969 + 3 ^ 40 * 1193485 * 2
def baseEnd_1193485 : Nat := 204277152977122739382923

theorem tailTrace_1193485 : CollatzResearch.WordTrace tailWord_1193485 prefixEnd_1193485 204277152977122739382923 := by
  unfold tailWord_1193485
  simp only [CollatzResearch.WordTrace]
  refine ⟨43529974081215150855293909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29019982720810100570195939 43529974081215150855293909)
  ·
    refine ⟨1020233767528480098170951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43529974081215150855293909 1020233767528480098170951)
    ·
      refine ⟨1530350651292720147256427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020233767528480098170951 1530350651292720147256427)
      ·
        refine ⟨2295525976939080220884641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530350651292720147256427 2295525976939080220884641)
        ·
          refine ⟨1721644482704310165663481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295525976939080220884641 1721644482704310165663481)
          ·
            refine ⟨1291233362028232624247611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721644482704310165663481 1291233362028232624247611)
            ·
              refine ⟨1936850043042348936371417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291233362028232624247611 1936850043042348936371417)
              ·
                refine ⟨1452637532281761702278563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936850043042348936371417 1452637532281761702278563)
                ·
                  refine ⟨2178956298422642553417845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452637532281761702278563 2178956298422642553417845)
                  ·
                    refine ⟨204277152977122739382923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2178956298422642553417845 204277152977122739382923)
                    ·
                      rfl

theorem cell23_1193485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1193485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193485 prefixEnd_1193485 := by exact prefixLift 1193485
  have htrace : WordTrace (prefixWord ++ tailWord_1193485) baseStart_1193485 baseEnd_1193485 := by
    simpa [prefixWord, tailWord_1193485, baseEnd_1193485] using wordTrace_append hprefix tailTrace_1193485
  have hstable : (prefixWord ++ tailWord_1193485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193485).length < 2 ^ (prefixWord ++ tailWord_1193485).sum := by decide
  have hdescent : baseEnd_1193485 < baseStart_1193485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193491 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 3]
def baseStart_1193491 : Nat := 118140960795 + 1193491 * 2 ^ 59
def prefixEnd_1193491 : Nat := 4983230072969 + 3 ^ 40 * 1193491 * 2
def baseEnd_1193491 : Nat := 612834539815295194673741

theorem tailTrace_1193491 : CollatzResearch.WordTrace tailWord_1193491 prefixEnd_1193491 612834539815295194673741 := by
  unfold tailWord_1193491
  simp only [CollatzResearch.WordTrace]
  refine ⟨43530192919193413880012327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29020128612795609253341551 43530192919193413880012327)
  ·
    refine ⟨65295289378790120820018491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43530192919193413880012327 65295289378790120820018491)
    ·
      refine ⟨97942934068185181230027737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65295289378790120820018491 97942934068185181230027737)
      ·
        refine ⟨73457200551138885922520803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97942934068185181230027737 73457200551138885922520803)
        ·
          refine ⟨110185800826708328883781205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73457200551138885922520803 110185800826708328883781205)
          ·
            refine ⟨1291239853437988229106811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 110185800826708328883781205 1291239853437988229106811)
            ·
              refine ⟨1936859780156982343660217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291239853437988229106811 1936859780156982343660217)
              ·
                refine ⟨1452644835117736757745163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936859780156982343660217 1452644835117736757745163)
                ·
                  refine ⟨2178967252676605136617745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452644835117736757745163 2178967252676605136617745)
                  ·
                    refine ⟨1634225439507453852463309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2178967252676605136617745 1634225439507453852463309)
                    ·
                      refine ⟨612834539815295194673741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634225439507453852463309 612834539815295194673741)
                      ·
                        rfl

theorem cell23_1193491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_1193491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193491 prefixEnd_1193491 := by exact prefixLift 1193491
  have htrace : WordTrace (prefixWord ++ tailWord_1193491) baseStart_1193491 baseEnd_1193491 := by
    simpa [prefixWord, tailWord_1193491, baseEnd_1193491] using wordTrace_append hprefix tailTrace_1193491
  have hstable : (prefixWord ++ tailWord_1193491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193491).length < 2 ^ (prefixWord ++ tailWord_1193491).sum := by decide
  have hdescent : baseEnd_1193491 < baseStart_1193491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193502 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1193502 : Nat := 118140960795 + 1193502 * 2 ^ 59
def prefixEnd_1193502 : Nat := 4983230072969 + 3 ^ 40 * 1193502 * 2
def baseEnd_1193502 : Nat := 204280062700831550545397

theorem tailTrace_1193502 : CollatzResearch.WordTrace tailWord_1193502 prefixEnd_1193502 204280062700831550545397 := by
  unfold tailWord_1193502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441324265269195344832845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29020396081435708505775173 5441324265269195344832845)
  ·
    refine ⟨2040496599475948254312317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5441324265269195344832845 2040496599475948254312317)
    ·
      refine ⟨765186224803480595367119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2040496599475948254312317 765186224803480595367119)
      ·
        refine ⟨1147779337205220893050679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765186224803480595367119 1147779337205220893050679)
        ·
          refine ⟨1721669005807831339576019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147779337205220893050679 1721669005807831339576019)
          ·
            refine ⟨2582503508711747009364029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721669005807831339576019 2582503508711747009364029)
            ·
              refine ⟨968438815766905128511511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2582503508711747009364029 968438815766905128511511)
              ·
                refine ⟨1452658223650357692767267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968438815766905128511511 1452658223650357692767267)
                ·
                  refine ⟨2178987335475536539150901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452658223650357692767267 2178987335475536539150901)
                  ·
                    refine ⟨204280062700831550545397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2178987335475536539150901 204280062700831550545397)
                    ·
                      rfl

theorem cell23_1193502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1193502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193502 prefixEnd_1193502 := by exact prefixLift 1193502
  have htrace : WordTrace (prefixWord ++ tailWord_1193502) baseStart_1193502 baseEnd_1193502 := by
    simpa [prefixWord, tailWord_1193502, baseEnd_1193502] using wordTrace_append hprefix tailTrace_1193502
  have hstable : (prefixWord ++ tailWord_1193502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193502).length < 2 ^ (prefixWord ++ tailWord_1193502).sum := by decide
  have hdescent : baseEnd_1193502 < baseStart_1193502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193504 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1193504 : Nat := 118140960795 + 1193504 * 2 ^ 59
def prefixEnd_1193504 : Nat := 4983230072969 + 3 ^ 40 * 1193504 * 2
def baseEnd_1193504 : Nat := 612841215063803643811181

theorem tailTrace_1193504 : CollatzResearch.WordTrace tailWord_1193504 prefixEnd_1193504 612841215063803643811181 := by
  unfold tailWord_1193504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21765333534073158550117783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29020444712097544733490377 21765333534073158550117783)
  ·
    refine ⟨32648000301109737825176675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21765333534073158550117783 32648000301109737825176675)
    ·
      refine ⟨48972000451664606737765013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32648000301109737825176675 48972000451664606737765013)
      ·
        refine ⟨2295562521171778440832735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48972000451664606737765013 2295562521171778440832735)
        ·
          refine ⟨3443343781757667661249103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295562521171778440832735 3443343781757667661249103)
          ·
            refine ⟨5165015672636501491873655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443343781757667661249103 5165015672636501491873655)
            ·
              refine ⟨7747523508954752237810483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165015672636501491873655 7747523508954752237810483)
              ·
                refine ⟨11621285263432128356715725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747523508954752237810483 11621285263432128356715725)
                ·
                  refine ⟨4357981973787048133768397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11621285263432128356715725 4357981973787048133768397)
                  ·
                    refine ⟨1634243240170143050163149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4357981973787048133768397 1634243240170143050163149)
                    ·
                      refine ⟨612841215063803643811181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634243240170143050163149 612841215063803643811181)
                      ·
                        rfl

theorem cell23_1193504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1193504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193504 prefixEnd_1193504 := by exact prefixLift 1193504
  have htrace : WordTrace (prefixWord ++ tailWord_1193504) baseStart_1193504 baseEnd_1193504 := by
    simpa [prefixWord, tailWord_1193504, baseEnd_1193504] using wordTrace_append hprefix tailTrace_1193504
  have hstable : (prefixWord ++ tailWord_1193504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193504).length < 2 ^ (prefixWord ++ tailWord_1193504).sum := by decide
  have hdescent : baseEnd_1193504 < baseStart_1193504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193527 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_1193527 : Nat := 118140960795 + 1193527 * 2 ^ 59
def prefixEnd_1193527 : Nat := 4983230072969 + 3 ^ 40 * 1193527 * 2
def baseEnd_1193527 : Nat := 612853025118857053823575

theorem tailTrace_1193527 : CollatzResearch.WordTrace tailWord_1193527 prefixEnd_1193527 612853025118857053823575 := by
  unfold tailWord_1193527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43531505947062992028322835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29021003964708661352215223 43531505947062992028322835)
  ·
    refine ⟨65297258920594488042484253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43531505947062992028322835 65297258920594488042484253)
    ·
      refine ⟨24486472095222933015931595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65297258920594488042484253 24486472095222933015931595)
      ·
        refine ⟨36729708142834399523897393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24486472095222933015931595 36729708142834399523897393)
        ·
          refine ⟨27547281107125799642923045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36729708142834399523897393 27547281107125799642923045)
          ·
            refine ⟨5165115207586087433048071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27547281107125799642923045 5165115207586087433048071)
            ·
              refine ⟨7747672811379131149572107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165115207586087433048071 7747672811379131149572107)
              ·
                refine ⟨11621509217068696724358161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7747672811379131149572107 11621509217068696724358161)
                ·
                  refine ⟨8716131912801522543268621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11621509217068696724358161 8716131912801522543268621)
                  ·
                    refine ⟨3268549467300570953725733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8716131912801522543268621 3268549467300570953725733)
                    ·
                      refine ⟨612853025118857053823575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3268549467300570953725733 612853025118857053823575)
                      ·
                        rfl

theorem cell23_1193527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_1193527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193527 prefixEnd_1193527 := by exact prefixLift 1193527
  have htrace : WordTrace (prefixWord ++ tailWord_1193527) baseStart_1193527 baseEnd_1193527 := by
    simpa [prefixWord, tailWord_1193527, baseEnd_1193527] using wordTrace_append hprefix tailTrace_1193527
  have hstable : (prefixWord ++ tailWord_1193527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193527).length < 2 ^ (prefixWord ++ tailWord_1193527).sum := by decide
  have hdescent : baseEnd_1193527 < baseStart_1193527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193547 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3]
def baseStart_1193547 : Nat := 118140960795 + 1193547 * 2 ^ 59
def prefixEnd_1193547 : Nat := 4983230072969 + 3 ^ 40 * 1193547 * 2
def baseEnd_1193547 : Nat := 612863294731946975573483

theorem tailTrace_1193547 : CollatzResearch.WordTrace tailWord_1193547 prefixEnd_1193547 612863294731946975573483 := by
  unfold tailWord_1193547
  simp only [CollatzResearch.WordTrace]
  refine ⟨43532235406990535444050895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29021490271327023629367263 43532235406990535444050895)
  ·
    refine ⟨65298353110485803166076343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43532235406990535444050895 65298353110485803166076343)
    ·
      refine ⟨97947529665728704749114515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65298353110485803166076343 97947529665728704749114515)
      ·
        refine ⟨146921294498593057123671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97947529665728704749114515 146921294498593057123671773)
        ·
          refine ⟨55095485436972396421376915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146921294498593057123671773 55095485436972396421376915)
          ·
            refine ⟨82643228155458594632065373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55095485436972396421376915 82643228155458594632065373)
            ·
              refine ⟨30991210558296972987024515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82643228155458594632065373 30991210558296972987024515)
              ·
                refine ⟨46486815837445459480536773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30991210558296972987024515 46486815837445459480536773)
                ·
                  refine ⟨8716277969521023652600645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46486815837445459480536773 8716277969521023652600645)
                  ·
                    refine ⟨1634302119285191934862621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8716277969521023652600645 1634302119285191934862621)
                    ·
                      refine ⟨612863294731946975573483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634302119285191934862621 612863294731946975573483)
                      ·
                        rfl

theorem cell23_1193547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3].length) (baseStart_1193547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193547 prefixEnd_1193547 := by exact prefixLift 1193547
  have htrace : WordTrace (prefixWord ++ tailWord_1193547) baseStart_1193547 baseEnd_1193547 := by
    simpa [prefixWord, tailWord_1193547, baseEnd_1193547] using wordTrace_append hprefix tailTrace_1193547
  have hstable : (prefixWord ++ tailWord_1193547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193547).length < 2 ^ (prefixWord ++ tailWord_1193547).sum := by decide
  have hdescent : baseEnd_1193547 < baseStart_1193547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193557 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1193557 : Nat := 118140960795 + 1193557 * 2 ^ 59
def prefixEnd_1193557 : Nat := 4983230072969 + 3 ^ 40 * 1193557 * 2
def baseEnd_1193557 : Nat := 612868429538491936448437

theorem tailTrace_1193557 : CollatzResearch.WordTrace tailWord_1193557 prefixEnd_1193557 612868429538491936448437 := by
  unfold tailWord_1193557
  simp only [CollatzResearch.WordTrace]
  refine ⟨43532600136954307151914925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29021733424636204767943283 43532600136954307151914925)
  ·
    refine ⟨16324725051357865181968097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43532600136954307151914925 16324725051357865181968097)
    ·
      refine ⟨12243543788518398886476073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16324725051357865181968097 12243543788518398886476073)
      ·
        refine ⟨9182657841388799164857055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12243543788518398886476073 9182657841388799164857055)
        ·
          refine ⟨13773986762083198747285583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9182657841388799164857055 13773986762083198747285583)
          ·
            refine ⟨20660980143124798120928375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13773986762083198747285583 20660980143124798120928375)
            ·
              refine ⟨30991470214687197181392563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20660980143124798120928375 30991470214687197181392563)
              ·
                refine ⟨46487205322030795772088845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30991470214687197181392563 46487205322030795772088845)
                ·
                  refine ⟨17432701995761548414533317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46487205322030795772088845 17432701995761548414533317)
                  ·
                    refine ⟨3268631624205290327724997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17432701995761548414533317 3268631624205290327724997)
                    ·
                      refine ⟨612868429538491936448437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3268631624205290327724997 612868429538491936448437)
                      ·
                        rfl

theorem cell23_1193557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1193557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193557 prefixEnd_1193557 := by exact prefixLift 1193557
  have htrace : WordTrace (prefixWord ++ tailWord_1193557) baseStart_1193557 baseEnd_1193557 := by
    simpa [prefixWord, tailWord_1193557, baseEnd_1193557] using wordTrace_append hprefix tailTrace_1193557
  have hstable : (prefixWord ++ tailWord_1193557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193557).length < 2 ^ (prefixWord ++ tailWord_1193557).sum := by decide
  have hdescent : baseEnd_1193557 < baseStart_1193557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193578 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1193578 : Nat := 118140960795 + 1193578 * 2 ^ 59
def prefixEnd_1193578 : Nat := 4983230072969 + 3 ^ 40 * 1193578 * 2
def baseEnd_1193578 : Nat := 612879212632236354285841

theorem tailTrace_1193578 : CollatzResearch.WordTrace tailWord_1193578 prefixEnd_1193578 612879212632236354285841 := by
  unfold tailWord_1193578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10883341517469556934607347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29022244046585485158952925 10883341517469556934607347)
  ·
    refine ⟨16325012276204335401911021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10883341517469556934607347 16325012276204335401911021)
    ·
      refine ⟨6121879603576625775716633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16325012276204335401911021 6121879603576625775716633)
      ·
        refine ⟨4591409702682469331787475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6121879603576625775716633 4591409702682469331787475)
        ·
          refine ⟨6887114554023703997681213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591409702682469331787475 6887114554023703997681213)
          ·
            refine ⟨2582667957758888999130455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6887114554023703997681213 2582667957758888999130455)
            ·
              refine ⟨3874001936638333498695683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582667957758888999130455 3874001936638333498695683)
              ·
                refine ⟨5811002904957500248043525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874001936638333498695683 5811002904957500248043525)
                ·
                  refine ⟨1089563044679531296508161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5811002904957500248043525 1089563044679531296508161)
                  ·
                    refine ⟨817172283509648472381121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089563044679531296508161 817172283509648472381121)
                    ·
                      refine ⟨612879212632236354285841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817172283509648472381121 612879212632236354285841)
                      ·
                        rfl

theorem cell23_1193578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1193578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193578 prefixEnd_1193578 := by exact prefixLift 1193578
  have htrace : WordTrace (prefixWord ++ tailWord_1193578) baseStart_1193578 baseEnd_1193578 := by
    simpa [prefixWord, tailWord_1193578, baseEnd_1193578] using wordTrace_append hprefix tailTrace_1193578
  have hstable : (prefixWord ++ tailWord_1193578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193578).length < 2 ^ (prefixWord ++ tailWord_1193578).sum := by decide
  have hdescent : baseEnd_1193578 < baseStart_1193578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193584 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 7]
def baseStart_1193584 : Nat := 118140960795 + 1193584 * 2 ^ 59
def prefixEnd_1193584 : Nat := 4983230072969 + 3 ^ 40 * 1193584 * 2
def baseEnd_1193584 : Nat := 68098032612907036756757

theorem tailTrace_1193584 : CollatzResearch.WordTrace tailWord_1193584 prefixEnd_1193584 68098032612907036756757 := by
  unfold tailWord_1193584
  simp only [CollatzResearch.WordTrace]
  refine ⟨21766792453928245381573903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29022389938570993842098537 21766792453928245381573903)
  ·
    refine ⟨32650188680892368072360855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21766792453928245381573903 32650188680892368072360855)
    ·
      refine ⟨48975283021338552108541283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32650188680892368072360855 48975283021338552108541283)
      ·
        refine ⟨73462924532007828162811925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48975283021338552108541283 73462924532007828162811925)
        ·
          refine ⟨3443574587437866945131809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73462924532007828162811925 3443574587437866945131809)
          ·
            refine ⟨2582680940578400208848857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3443574587437866945131809 2582680940578400208848857)
            ·
              refine ⟨1937010705433800156636643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582680940578400208848857 1937010705433800156636643)
              ·
                refine ⟨2905516058150700234954965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937010705433800156636643 2905516058150700234954965)
                ·
                  refine ⟨68098032612907036756757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2905516058150700234954965 68098032612907036756757)
                  ·
                    rfl

theorem cell23_1193584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_1193584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193584 prefixEnd_1193584 := by exact prefixLift 1193584
  have htrace : WordTrace (prefixWord ++ tailWord_1193584) baseStart_1193584 baseEnd_1193584 := by
    simpa [prefixWord, tailWord_1193584, baseEnd_1193584] using wordTrace_append hprefix tailTrace_1193584
  have hstable : (prefixWord ++ tailWord_1193584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193584).length < 2 ^ (prefixWord ++ tailWord_1193584).sum := by decide
  have hdescent : baseEnd_1193584 < baseStart_1193584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193614 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1193614 : Nat := 118140960795 + 1193614 * 2 ^ 59
def prefixEnd_1193614 : Nat := 4983230072969 + 3 ^ 40 * 1193614 * 2
def baseEnd_1193614 : Nat := 204299232645266071145225

theorem tailTrace_1193614 : CollatzResearch.WordTrace tailWord_1193614 prefixEnd_1193614 204299232645266071145225 := by
  unfold tailWord_1193614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441834887218475735842487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29023119398498537257826597 5441834887218475735842487)
  ·
    refine ⟨8162752330827713603763731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441834887218475735842487 8162752330827713603763731)
    ·
      refine ⟨12244128496241570405645597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8162752330827713603763731 12244128496241570405645597)
      ·
        refine ⟨4591548186090588902117099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12244128496241570405645597 4591548186090588902117099)
        ·
          refine ⟨6887322279135883353175649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591548186090588902117099 6887322279135883353175649)
          ·
            refine ⟨5165491709351912514881737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6887322279135883353175649 5165491709351912514881737)
            ·
              refine ⟨3874118782013934386161303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165491709351912514881737 3874118782013934386161303)
              ·
                refine ⟨5811178173020901579241955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874118782013934386161303 5811178173020901579241955)
                ·
                  refine ⟨8716767259531352368862933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811178173020901579241955 8716767259531352368862933)
                  ·
                    refine ⟨204299232645266071145225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8716767259531352368862933 204299232645266071145225)
                    ·
                      rfl

theorem cell23_1193614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1193614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193614 prefixEnd_1193614 := by exact prefixLift 1193614
  have htrace : WordTrace (prefixWord ++ tailWord_1193614) baseStart_1193614 baseEnd_1193614 := by
    simpa [prefixWord, tailWord_1193614, baseEnd_1193614] using wordTrace_append hprefix tailTrace_1193614
  have hstable : (prefixWord ++ tailWord_1193614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193614).length < 2 ^ (prefixWord ++ tailWord_1193614).sum := by decide
  have hdescent : baseEnd_1193614 < baseStart_1193614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193646 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1193646 : Nat := 118140960795 + 1193646 * 2 ^ 59
def prefixEnd_1193646 : Nat := 4983230072969 + 3 ^ 40 * 1193646 * 2
def baseEnd_1193646 : Nat := 612914129316742088235529

theorem tailTrace_1193646 : CollatzResearch.WordTrace tailWord_1193646 prefixEnd_1193646 612914129316742088235529 := by
  unfold tailWord_1193646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441980779203984418988099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29023897489087916901269861 5441980779203984418988099)
  ·
    refine ⟨8162971168805976628482149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441980779203984418988099 8162971168805976628482149)
    ·
      refine ⟨1530557094151120617840403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8162971168805976628482149 1530557094151120617840403)
      ·
        refine ⟨2295835641226680926760605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530557094151120617840403 2295835641226680926760605)
        ·
          refine ⟨860938365460005347535227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2295835641226680926760605 860938365460005347535227)
          ·
            refine ⟨1291407548190008021302841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860938365460005347535227 1291407548190008021302841)
            ·
              refine ⟨968555661142506015977131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291407548190008021302841 968555661142506015977131)
              ·
                refine ⟨1452833491713759023965697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968555661142506015977131 1452833491713759023965697)
                ·
                  refine ⟨1089625118785319267974273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1452833491713759023965697 1089625118785319267974273)
                  ·
                    refine ⟨817218839088989450980705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089625118785319267974273 817218839088989450980705)
                    ·
                      refine ⟨612914129316742088235529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817218839088989450980705 612914129316742088235529)
                      ·
                        rfl

theorem cell23_1193646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1193646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193646 prefixEnd_1193646 := by exact prefixLift 1193646
  have htrace : WordTrace (prefixWord ++ tailWord_1193646) baseStart_1193646 baseEnd_1193646 := by
    simpa [prefixWord, tailWord_1193646, baseEnd_1193646] using wordTrace_append hprefix tailTrace_1193646
  have hstable : (prefixWord ++ tailWord_1193646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193646).length < 2 ^ (prefixWord ++ tailWord_1193646).sum := by decide
  have hdescent : baseEnd_1193646 < baseStart_1193646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193671 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1193671 : Nat := 118140960795 + 1193671 * 2 ^ 59
def prefixEnd_1193671 : Nat := 4983230072969 + 3 ^ 40 * 1193671 * 2
def baseEnd_1193671 : Nat := 612926966333104490422913

theorem tailTrace_1193671 : CollatzResearch.WordTrace tailWord_1193671 prefixEnd_1193671 612926966333104490422913 := by
  unfold tailWord_1193671
  simp only [CollatzResearch.WordTrace]
  refine ⟨43536758058541304621564867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29024505372360869747709911 43536758058541304621564867)
  ·
    refine ⟨65305137087811956932347301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43536758058541304621564867 65305137087811956932347301)
    ·
      refine ⟨12244713203964741924815119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65305137087811956932347301 12244713203964741924815119)
      ·
        refine ⟨18367069805947112887222679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12244713203964741924815119 18367069805947112887222679)
        ·
          refine ⟨27550604708920669330834019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18367069805947112887222679 27550604708920669330834019)
          ·
            refine ⟨41325907063381003996251029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27550604708920669330834019 41325907063381003996251029)
            ·
              refine ⟨1937151893595984562324267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41325907063381003996251029 1937151893595984562324267)
              ·
                refine ⟨2905727840393976843486401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937151893595984562324267 2905727840393976843486401)
                ·
                  refine ⟨2179295880295482632614801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2905727840393976843486401 2179295880295482632614801)
                  ·
                    refine ⟨1634471910221611974461101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2179295880295482632614801 1634471910221611974461101)
                    ·
                      refine ⟨612926966333104490422913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634471910221611974461101 612926966333104490422913)
                      ·
                        rfl

theorem cell23_1193671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1193671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193671 prefixEnd_1193671 := by exact prefixLift 1193671
  have htrace : WordTrace (prefixWord ++ tailWord_1193671) baseStart_1193671 baseEnd_1193671 := by
    simpa [prefixWord, tailWord_1193671, baseEnd_1193671] using wordTrace_append hprefix tailTrace_1193671
  have hstable : (prefixWord ++ tailWord_1193671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193671).length < 2 ^ (prefixWord ++ tailWord_1193671).sum := by decide
  have hdescent : baseEnd_1193671 < baseStart_1193671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193678 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_1193678 : Nat := 118140960795 + 1193678 * 2 ^ 59
def prefixEnd_1193678 : Nat := 4983230072969 + 3 ^ 40 * 1193678 * 2
def baseEnd_1193678 : Nat := 204310186899228654345127

theorem tailTrace_1193678 : CollatzResearch.WordTrace tailWord_1193678 prefixEnd_1193678 204310186899228654345127 := by
  unfold tailWord_1193678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442126671189493102133711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29024675579677296544713125 5442126671189493102133711)
  ·
    refine ⟨8163190006784239653200567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442126671189493102133711 8163190006784239653200567)
    ·
      refine ⟨12244785010176359479800851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8163190006784239653200567 12244785010176359479800851)
      ·
        refine ⟨18367177515264539219701277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12244785010176359479800851 18367177515264539219701277)
        ·
          refine ⟨6887691568224202207387979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18367177515264539219701277 6887691568224202207387979)
          ·
            refine ⟨10331537352336303311081969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887691568224202207387979 10331537352336303311081969)
            ·
              refine ⟨7748653014252227483311477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10331537352336303311081969 7748653014252227483311477)
              ·
                refine ⟨726436220086146326560451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7748653014252227483311477 726436220086146326560451)
                ·
                  refine ⟨1089654330129219489840677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726436220086146326560451 1089654330129219489840677)
                  ·
                    refine ⟨204310186899228654345127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089654330129219489840677 204310186899228654345127)
                    ·
                      rfl

theorem cell23_1193678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_1193678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193678 prefixEnd_1193678 := by exact prefixLift 1193678
  have htrace : WordTrace (prefixWord ++ tailWord_1193678) baseStart_1193678 baseEnd_1193678 := by
    simpa [prefixWord, tailWord_1193678, baseEnd_1193678] using wordTrace_append hprefix tailTrace_1193678
  have hstable : (prefixWord ++ tailWord_1193678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193678).length < 2 ^ (prefixWord ++ tailWord_1193678).sum := by decide
  have hdescent : baseEnd_1193678 < baseStart_1193678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193711 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 5, 2]
def baseStart_1193711 : Nat := 118140960795 + 1193711 * 2 ^ 59
def prefixEnd_1193711 : Nat := 4983230072969 + 3 ^ 40 * 1193711 * 2
def baseEnd_1193711 : Nat := 612947505559284333922729

theorem tailTrace_1193711 : CollatzResearch.WordTrace tailWord_1193711 prefixEnd_1193711 612947505559284333922729 := by
  unfold tailWord_1193711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43538216978396391453020987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29025477985597594302013991 43538216978396391453020987)
  ·
    refine ⟨65307325467594587179531481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43538216978396391453020987 65307325467594587179531481)
    ·
      refine ⟨48980494100695940384648611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65307325467594587179531481 48980494100695940384648611)
      ·
        refine ⟨73470741151043910576972917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48980494100695940384648611 73470741151043910576972917)
        ·
          refine ⟨6887881982910366616591211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73470741151043910576972917 6887881982910366616591211)
          ·
            refine ⟨10331822974365549924886817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887881982910366616591211 10331822974365549924886817)
            ·
              refine ⟨7748867230774162443665113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10331822974365549924886817 7748867230774162443665113)
              ·
                refine ⟨5811650423080621832748835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7748867230774162443665113 5811650423080621832748835)
                ·
                  refine ⟨8717475634620932749123253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811650423080621832748835 8717475634620932749123253)
                  ·
                    refine ⟨817263340745712445230305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8717475634620932749123253 817263340745712445230305)
                    ·
                      refine ⟨612947505559284333922729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817263340745712445230305 612947505559284333922729)
                      ·
                        rfl

theorem cell23_1193711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5, 2].length) (baseStart_1193711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193711 prefixEnd_1193711 := by exact prefixLift 1193711
  have htrace : WordTrace (prefixWord ++ tailWord_1193711) baseStart_1193711 baseEnd_1193711 := by
    simpa [prefixWord, tailWord_1193711, baseEnd_1193711] using wordTrace_append hprefix tailTrace_1193711
  have hstable : (prefixWord ++ tailWord_1193711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193711).length < 2 ^ (prefixWord ++ tailWord_1193711).sum := by decide
  have hdescent : baseEnd_1193711 < baseStart_1193711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193714 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1193714 : Nat := 118140960795 + 1193714 * 2 ^ 59
def prefixEnd_1193714 : Nat := 4983230072969 + 3 ^ 40 * 1193714 * 2
def baseEnd_1193714 : Nat := 612949046001247822185215

theorem tailTrace_1193714 : CollatzResearch.WordTrace tailWord_1193714 prefixEnd_1193714 612949046001247822185215 := by
  unfold tailWord_1193714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884581599346380741345049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29025550931590348643586797 10884581599346380741345049)
  ·
    refine ⟨8163436199509785556008787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10884581599346380741345049 8163436199509785556008787)
    ·
      refine ⟨12245154299264678334013181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8163436199509785556008787 12245154299264678334013181)
      ·
        refine ⟨4591932862224254375254943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12245154299264678334013181 4591932862224254375254943)
        ·
          refine ⟨6887899293336381562882415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591932862224254375254943 6887899293336381562882415)
          ·
            refine ⟨10331848940004572344323623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887899293336381562882415 10331848940004572344323623)
            ·
              refine ⟨15497773410006858516485435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10331848940004572344323623 15497773410006858516485435)
              ·
                refine ⟨23246660115010287774728153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15497773410006858516485435 23246660115010287774728153)
                ·
                  refine ⟨17434995086257715831046115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23246660115010287774728153 17434995086257715831046115)
                  ·
                    refine ⟨26152492629386573746569173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17434995086257715831046115 26152492629386573746569173)
                    ·
                      refine ⟨612949046001247822185215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26152492629386573746569173 612949046001247822185215)
                      ·
                        rfl

theorem cell23_1193714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1193714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193714 prefixEnd_1193714 := by exact prefixLift 1193714
  have htrace : WordTrace (prefixWord ++ tailWord_1193714) baseStart_1193714 baseEnd_1193714 := by
    simpa [prefixWord, tailWord_1193714, baseEnd_1193714] using wordTrace_append hprefix tailTrace_1193714
  have hstable : (prefixWord ++ tailWord_1193714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193714).length < 2 ^ (prefixWord ++ tailWord_1193714).sum := by decide
  have hdescent : baseEnd_1193714 < baseStart_1193714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193718 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1193718 : Nat := 118140960795 + 1193718 * 2 ^ 59
def prefixEnd_1193718 : Nat := 4983230072969 + 3 ^ 40 * 1193718 * 2
def baseEnd_1193718 : Nat := 612951099923865806535197

theorem tailTrace_1193718 : CollatzResearch.WordTrace tailWord_1193718 prefixEnd_1193718 612951099923865806535197 := by
  unfold tailWord_1193718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721154518085689478032863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29025648192914021099017205 2721154518085689478032863)
  ·
    refine ⟨4081731777128534217049295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2721154518085689478032863 4081731777128534217049295)
    ·
      refine ⟨6122597665692801325573943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081731777128534217049295 6122597665692801325573943)
      ·
        refine ⟨9183896498539201988360915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122597665692801325573943 9183896498539201988360915)
        ·
          refine ⟨13775844747808802982541373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9183896498539201988360915 13775844747808802982541373)
          ·
            refine ⟨5165941780428301118453015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13775844747808802982541373 5165941780428301118453015)
            ·
              refine ⟨7748912670642451677679523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165941780428301118453015 7748912670642451677679523)
              ·
                refine ⟨11623369005963677516519285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748912670642451677679523 11623369005963677516519285)
                ·
                  refine ⟨1089690844309094767173683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11623369005963677516519285 1089690844309094767173683)
                  ·
                    refine ⟨1634536266463642150760525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1089690844309094767173683 1634536266463642150760525)
                    ·
                      refine ⟨612951099923865806535197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634536266463642150760525 612951099923865806535197)
                      ·
                        rfl

theorem cell23_1193718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1193718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193718 prefixEnd_1193718 := by exact prefixLift 1193718
  have htrace : WordTrace (prefixWord ++ tailWord_1193718) baseStart_1193718 baseEnd_1193718 := by
    simpa [prefixWord, tailWord_1193718, baseEnd_1193718] using wordTrace_append hprefix tailTrace_1193718
  have hstable : (prefixWord ++ tailWord_1193718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193718).length < 2 ^ (prefixWord ++ tailWord_1193718).sum := by decide
  have hdescent : baseEnd_1193718 < baseStart_1193718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193738 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_1193738 : Nat := 118140960795 + 1193738 * 2 ^ 59
def prefixEnd_1193738 : Nat := 4983230072969 + 3 ^ 40 * 1193738 * 2
def baseEnd_1193738 : Nat := 204320456512318576095035

theorem tailTrace_1193738 : CollatzResearch.WordTrace tailWord_1193738 prefixEnd_1193738 204320456512318576095035 := by
  unfold tailWord_1193738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884800437324643766063467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29026134499532383376169245 10884800437324643766063467)
  ·
    refine ⟨16327200655986965649095201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10884800437324643766063467 16327200655986965649095201)
    ·
      refine ⟨12245400491990224236821401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16327200655986965649095201 12245400491990224236821401)
      ·
        refine ⟨9184050368992668177616051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12245400491990224236821401 9184050368992668177616051)
        ·
          refine ⟨13776075553489002266424077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9184050368992668177616051 13776075553489002266424077)
          ·
            refine ⟨5166028332558375849909029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13776075553489002266424077 5166028332558375849909029)
            ·
              refine ⟨968630312354695471857943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5166028332558375849909029 968630312354695471857943)
              ·
                refine ⟨1452945468532043207786915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968630312354695471857943 1452945468532043207786915)
                ·
                  refine ⟨2179418202798064811680373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452945468532043207786915 2179418202798064811680373)
                  ·
                    refine ⟨204320456512318576095035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2179418202798064811680373 204320456512318576095035)
                    ·
                      rfl

theorem cell23_1193738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_1193738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193738 prefixEnd_1193738 := by exact prefixLift 1193738
  have htrace : WordTrace (prefixWord ++ tailWord_1193738) baseStart_1193738 baseEnd_1193738 := by
    simpa [prefixWord, tailWord_1193738, baseEnd_1193738] using wordTrace_append hprefix tailTrace_1193738
  have hstable : (prefixWord ++ tailWord_1193738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193738).length < 2 ^ (prefixWord ++ tailWord_1193738).sum := by decide
  have hdescent : baseEnd_1193738 < baseStart_1193738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193761 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1193761 : Nat := 118140960795 + 1193761 * 2 ^ 59
def prefixEnd_1193761 : Nat := 4983230072969 + 3 ^ 40 * 1193761 * 2
def baseEnd_1193761 : Nat := 612973179592009138297499

theorem tailTrace_1193761 : CollatzResearch.WordTrace tailWord_1193761 prefixEnd_1193761 612973179592009138297499 := by
  unfold tailWord_1193761
  simp only [CollatzResearch.WordTrace]
  refine ⟨43540040628215249992341137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29026693752143499994894091 43540040628215249992341137)
  ·
    refine ⟨32655030471161437494255853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43540040628215249992341137 32655030471161437494255853)
    ·
      refine ⟨12245636426685539060345945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32655030471161437494255853 12245636426685539060345945)
      ·
        refine ⟨9184227320014154295259459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12245636426685539060345945 9184227320014154295259459)
        ·
          refine ⟨13776340980021231442889189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9184227320014154295259459 13776340980021231442889189)
          ·
            refine ⟨2583063933753980895541723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13776340980021231442889189 2583063933753980895541723)
            ·
              refine ⟨3874595900630971343312585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583063933753980895541723 3874595900630971343312585)
              ·
                refine ⟨2905946925473228507484439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874595900630971343312585 2905946925473228507484439)
                ·
                  refine ⟨4358920388209842761226659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905946925473228507484439 4358920388209842761226659)
                  ·
                    refine ⟨6538380582314764141839989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4358920388209842761226659 6538380582314764141839989)
                    ·
                      refine ⟨612973179592009138297499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6538380582314764141839989 612973179592009138297499)
                      ·
                        rfl

theorem cell23_1193761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1193761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193761 prefixEnd_1193761 := by exact prefixLift 1193761
  have htrace : WordTrace (prefixWord ++ tailWord_1193761) baseStart_1193761 baseEnd_1193761 := by
    simpa [prefixWord, tailWord_1193761, baseEnd_1193761] using wordTrace_append hprefix tailTrace_1193761
  have hstable : (prefixWord ++ tailWord_1193761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193761).length < 2 ^ (prefixWord ++ tailWord_1193761).sum := by decide
  have hdescent : baseEnd_1193761 < baseStart_1193761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193768 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1193768 : Nat := 118140960795 + 1193768 * 2 ^ 59
def prefixEnd_1193768 : Nat := 4983230072969 + 3 ^ 40 * 1193768 * 2
def baseEnd_1193768 : Nat := 204325591318863536969989

theorem tailTrace_1193768 : CollatzResearch.WordTrace tailWord_1193768 prefixEnd_1193768 204325591318863536969989 := by
  unfold tailWord_1193768
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770147969594945093922979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29026863959459926791897305 21770147969594945093922979)
  ·
    refine ⟨32655221954392417640884469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21770147969594945093922979 32655221954392417640884469)
    ·
      refine ⟨3061427058224289153832919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32655221954392417640884469 3061427058224289153832919)
      ·
        refine ⟨4592140587336433730749379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061427058224289153832919 4592140587336433730749379)
        ·
          refine ⟨6888210881004650596124069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592140587336433730749379 6888210881004650596124069)
          ·
            refine ⟨1291539540188371986773263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6888210881004650596124069 1291539540188371986773263)
            ·
              refine ⟨1937309310282557980159895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291539540188371986773263 1937309310282557980159895)
              ·
                refine ⟨2905963965423836970239843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937309310282557980159895 2905963965423836970239843)
                ·
                  refine ⟨4358945948135755455359765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905963965423836970239843 4358945948135755455359765)
                  ·
                    refine ⟨204325591318863536969989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4358945948135755455359765 204325591318863536969989)
                    ·
                      rfl

theorem cell23_1193768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1193768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193768 prefixEnd_1193768 := by exact prefixLift 1193768
  have htrace : WordTrace (prefixWord ++ tailWord_1193768) baseStart_1193768 baseEnd_1193768 := by
    simpa [prefixWord, tailWord_1193768, baseEnd_1193768] using wordTrace_append hprefix tailTrace_1193768
  have hstable : (prefixWord ++ tailWord_1193768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193768).length < 2 ^ (prefixWord ++ tailWord_1193768).sum := by decide
  have hdescent : baseEnd_1193768 < baseStart_1193768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193778 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1193778 : Nat := 118140960795 + 1193778 * 2 ^ 59
def prefixEnd_1193778 : Nat := 4983230072969 + 3 ^ 40 * 1193778 * 2
def baseEnd_1193778 : Nat := 612981908763135571784921

theorem tailTrace_1193778 : CollatzResearch.WordTrace tailWord_1193778 prefixEnd_1193778 612981908763135571784921 := by
  unfold tailWord_1193778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885165167288415473927497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29027107112769107930473325 10885165167288415473927497)
  ·
    refine ⟨8163873875466311605445623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10885165167288415473927497 8163873875466311605445623)
    ·
      refine ⟨12245810813199467408168435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8163873875466311605445623 12245810813199467408168435)
      ·
        refine ⟨18368716219799201112252653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12245810813199467408168435 18368716219799201112252653)
        ·
          refine ⟨6888268582424700417094745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18368716219799201112252653 6888268582424700417094745)
          ·
            refine ⟨5166201436818525312821059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6888268582424700417094745 5166201436818525312821059)
            ·
              refine ⟨7749302155227787969231589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166201436818525312821059 7749302155227787969231589)
              ·
                refine ⟨1452994154105210244230923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7749302155227787969231589 1452994154105210244230923)
                ·
                  refine ⟨2179491231157815366346385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452994154105210244230923 2179491231157815366346385)
                  ·
                    refine ⟨1634618423368361524759789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2179491231157815366346385 1634618423368361524759789)
                    ·
                      refine ⟨612981908763135571784921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634618423368361524759789 612981908763135571784921)
                      ·
                        rfl

theorem cell23_1193778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1193778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193778 prefixEnd_1193778 := by exact prefixLift 1193778
  have htrace : WordTrace (prefixWord ++ tailWord_1193778) baseStart_1193778 baseEnd_1193778 := by
    simpa [prefixWord, tailWord_1193778, baseEnd_1193778] using wordTrace_append hprefix tailTrace_1193778
  have hstable : (prefixWord ++ tailWord_1193778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193778).length < 2 ^ (prefixWord ++ tailWord_1193778).sum := by decide
  have hdescent : baseEnd_1193778 < baseStart_1193778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193781 : List Nat := [1, 3, 3, 1, 4, 1, 1, 9]
def baseStart_1193781 : Nat := 118140960795 + 1193781 * 2 ^ 59
def prefixEnd_1193781 : Nat := 4983230072969 + 3 ^ 40 * 1193781 * 2
def baseEnd_1193781 : Nat := 22703090711299965186941

theorem tailTrace_1193781 : CollatzResearch.WordTrace tailWord_1193781 prefixEnd_1193781 22703090711299965186941 := by
  unfold tailWord_1193781
  simp only [CollatzResearch.WordTrace]
  refine ⟨43540770088142793408069197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29027180058761862272046131 43540770088142793408069197)
  ·
    refine ⟨16327788783053547528025949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43540770088142793408069197 16327788783053547528025949)
    ·
      refine ⟨6122920793645080323009731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16327788783053547528025949 6122920793645080323009731)
      ·
        refine ⟨9184381190467620484514597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122920793645080323009731 9184381190467620484514597)
        ·
          refine ⟨1722071473212678840846487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9184381190467620484514597 1722071473212678840846487)
          ·
            refine ⟨2583107209819018261269731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722071473212678840846487 2583107209819018261269731)
            ·
              refine ⟨3874660814728527391904597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583107209819018261269731 3874660814728527391904597)
              ·
                refine ⟨22703090711299965186941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3874660814728527391904597 22703090711299965186941)
                ·
                  rfl

theorem cell23_1193781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 9].length) (baseStart_1193781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193781 prefixEnd_1193781 := by exact prefixLift 1193781
  have htrace : WordTrace (prefixWord ++ tailWord_1193781) baseStart_1193781 baseEnd_1193781 := by
    simpa [prefixWord, tailWord_1193781, baseEnd_1193781] using wordTrace_append hprefix tailTrace_1193781
  have hstable : (prefixWord ++ tailWord_1193781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193781).length < 2 ^ (prefixWord ++ tailWord_1193781).sum := by decide
  have hdescent : baseEnd_1193781 < baseStart_1193781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193798 : List Nat := [6, 1, 1, 2, 1, 1, 11]
def baseStart_1193798 : Nat := 118140960795 + 1193798 * 2 ^ 59
def prefixEnd_1193798 : Nat := 4983230072969 + 3 ^ 40 * 1193798 * 2
def baseEnd_1193798 : Nat := 7567804671311425846109

theorem tailTrace_1193798 : CollatzResearch.WordTrace tailWord_1193798 prefixEnd_1193798 7567804671311425846109 := by
  unfold tailWord_1193798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360668441533787665982439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29027593419387470207625365 1360668441533787665982439)
  ·
    refine ⟨2041002662300681498973659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360668441533787665982439 2041002662300681498973659)
    ·
      refine ⟨3061503993451022248460489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041002662300681498973659 3061503993451022248460489)
      ·
        refine ⟨2296127995088266686345367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061503993451022248460489 2296127995088266686345367)
        ·
          refine ⟨3444191992632400029518051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296127995088266686345367 3444191992632400029518051)
          ·
            refine ⟨5166287988948600044277077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444191992632400029518051 5166287988948600044277077)
            ·
              refine ⟨7567804671311425846109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5166287988948600044277077 7567804671311425846109)
              ·
                rfl

theorem cell23_1193798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 11].length) (baseStart_1193798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193798 prefixEnd_1193798 := by exact prefixLift 1193798
  have htrace : WordTrace (prefixWord ++ tailWord_1193798) baseStart_1193798 baseEnd_1193798 := by
    simpa [prefixWord, tailWord_1193798, baseEnd_1193798] using wordTrace_append hprefix tailTrace_1193798
  have hstable : (prefixWord ++ tailWord_1193798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193798).length < 2 ^ (prefixWord ++ tailWord_1193798).sum := by decide
  have hdescent : baseEnd_1193798 < baseStart_1193798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193808 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3]
def baseStart_1193808 : Nat := 118140960795 + 1193808 * 2 ^ 59
def prefixEnd_1193808 : Nat := 4983230072969 + 3 ^ 40 * 1193808 * 2
def baseEnd_1193808 : Nat := 612997313182770454409783

theorem tailTrace_1193808 : CollatzResearch.WordTrace tailWord_1193808 prefixEnd_1193808 612997313182770454409783 := by
  unfold tailWord_1193808
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770877429522488509651039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29027836572696651346201385 21770877429522488509651039)
  ·
    refine ⟨32656316144283732764476559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21770877429522488509651039 32656316144283732764476559)
    ·
      refine ⟨48984474216425599146714839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32656316144283732764476559 48984474216425599146714839)
      ·
        refine ⟨73476711324638398720072259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48984474216425599146714839 73476711324638398720072259)
        ·
          refine ⟨110215066986957598080108389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73476711324638398720072259 110215066986957598080108389)
          ·
            refine ⟨20665325060054549640020323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110215066986957598080108389 20665325060054549640020323)
            ·
              refine ⟨30997987590081824460030485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20665325060054549640020323 30997987590081824460030485)
              ·
                refine ⟨1453030668285085521563929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30997987590081824460030485 1453030668285085521563929)
                ·
                  refine ⟨1089773001213814141172947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1453030668285085521563929 1089773001213814141172947)
                  ·
                    refine ⟨1634659501820721211759421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1089773001213814141172947 1634659501820721211759421)
                    ·
                      refine ⟨612997313182770454409783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634659501820721211759421 612997313182770454409783)
                      ·
                        rfl

theorem cell23_1193808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_1193808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193808 prefixEnd_1193808 := by exact prefixLift 1193808
  have htrace : WordTrace (prefixWord ++ tailWord_1193808) baseStart_1193808 baseEnd_1193808 := by
    simpa [prefixWord, tailWord_1193808, baseEnd_1193808] using wordTrace_append hprefix tailTrace_1193808
  have hstable : (prefixWord ++ tailWord_1193808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193808).length < 2 ^ (prefixWord ++ tailWord_1193808).sum := by decide
  have hdescent : baseEnd_1193808 < baseStart_1193808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193809 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 1, 2, 2]
def baseStart_1193809 : Nat := 118140960795 + 1193809 * 2 ^ 59
def prefixEnd_1193809 : Nat := 4983230072969 + 3 ^ 40 * 1193809 * 2
def baseEnd_1193809 : Nat := 612997826663424950497279

theorem tailTrace_1193809 : CollatzResearch.WordTrace tailWord_1193809 prefixEnd_1193809 612997826663424950497279 := by
  unfold tailWord_1193809
  simp only [CollatzResearch.WordTrace]
  refine ⟨43541791332041354190088481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29027860888027569460058987 43541791332041354190088481)
  ·
    refine ⟨32656343499031015642566361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43541791332041354190088481 32656343499031015642566361)
    ·
      refine ⟨24492257624273261731924771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32656343499031015642566361 24492257624273261731924771)
      ·
        refine ⟨36738386436409892597887157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24492257624273261731924771 36738386436409892597887157)
        ·
          refine ⟨3444223728413427431051921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36738386436409892597887157 3444223728413427431051921)
          ·
            refine ⟨2583167796310070573288941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3444223728413427431051921 2583167796310070573288941)
            ·
              refine ⟨968687923616276464983353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2583167796310070573288941 968687923616276464983353)
              ·
                refine ⟨726515942712207348737515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968687923616276464983353 726515942712207348737515)
                ·
                  refine ⟨1089773914068311023106273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726515942712207348737515 1089773914068311023106273)
                  ·
                    refine ⟨817330435551233267329705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089773914068311023106273 817330435551233267329705)
                    ·
                      refine ⟨612997826663424950497279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817330435551233267329705 612997826663424950497279)
                      ·
                        rfl

theorem cell23_1193809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_1193809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193809 prefixEnd_1193809 := by exact prefixLift 1193809
  have htrace : WordTrace (prefixWord ++ tailWord_1193809) baseStart_1193809 baseEnd_1193809 := by
    simpa [prefixWord, tailWord_1193809, baseEnd_1193809] using wordTrace_append hprefix tailTrace_1193809
  have hstable : (prefixWord ++ tailWord_1193809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193809).length < 2 ^ (prefixWord ++ tailWord_1193809).sum := by decide
  have hdescent : baseEnd_1193809 < baseStart_1193809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193818 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_1193818 : Nat := 118140960795 + 1193818 * 2 ^ 59
def prefixEnd_1193818 : Nat := 4983230072969 + 3 ^ 40 * 1193818 * 2
def baseEnd_1193818 : Nat := 613002447989315415284737

theorem tailTrace_1193818 : CollatzResearch.WordTrace tailWord_1193818 prefixEnd_1193818 613002447989315415284737 := by
  unfold tailWord_1193818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885529897252187181791527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29028079726005832484777405 10885529897252187181791527)
  ·
    refine ⟨16328294845878280772687291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10885529897252187181791527 16328294845878280772687291)
    ·
      refine ⟨24492442268817421159030937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16328294845878280772687291 24492442268817421159030937)
      ·
        refine ⟨18369331701613065869273203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24492442268817421159030937 18369331701613065869273203)
        ·
          refine ⟨27553997552419598803909805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18369331701613065869273203 27553997552419598803909805)
          ·
            refine ⟨10332749082157349551466177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27553997552419598803909805 10332749082157349551466177)
            ·
              refine ⟨7749561811618012163599633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10332749082157349551466177 7749561811618012163599633)
              ·
                refine ⟨5812171358713509122699725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7749561811618012163599633 5812171358713509122699725)
                ·
                  refine ⟨2179564259517565921012397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5812171358713509122699725 2179564259517565921012397)
                  ·
                    refine ⟨817336597319087220379649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179564259517565921012397 817336597319087220379649)
                    ·
                      refine ⟨613002447989315415284737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817336597319087220379649 613002447989315415284737)
                      ·
                        rfl

theorem cell23_1193818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_1193818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193818 prefixEnd_1193818 := by exact prefixLift 1193818
  have htrace : WordTrace (prefixWord ++ tailWord_1193818) baseStart_1193818 baseEnd_1193818 := by
    simpa [prefixWord, tailWord_1193818, baseEnd_1193818] using wordTrace_append hprefix tailTrace_1193818
  have hstable : (prefixWord ++ tailWord_1193818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193818).length < 2 ^ (prefixWord ++ tailWord_1193818).sum := by decide
  have hdescent : baseEnd_1193818 < baseStart_1193818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193861 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_1193861 : Nat := 118140960795 + 1193861 * 2 ^ 59
def prefixEnd_1193861 : Nat := 4983230072969 + 3 ^ 40 * 1193861 * 2
def baseEnd_1193861 : Nat := 613024527657458747047039

theorem tailTrace_1193861 : CollatzResearch.WordTrace tailWord_1193861 prefixEnd_1193861 613024527657458747047039 := by
  unfold tailWord_1193861
  simp only [CollatzResearch.WordTrace]
  refine ⟨43543687927852967070981437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29029125285235311380654291 43543687927852967070981437)
  ·
    refine ⟨16328882972944862651618039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43543687927852967070981437 16328882972944862651618039)
    ·
      refine ⟨24493324459417293977427059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16328882972944862651618039 24493324459417293977427059)
      ·
        refine ⟨36739986689125940966140589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24493324459417293977427059 36739986689125940966140589)
        ·
          refine ⟨13777495008422227862302721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36739986689125940966140589 13777495008422227862302721)
          ·
            refine ⟨10333121256316670896727041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13777495008422227862302721 10333121256316670896727041)
            ·
              refine ⟨7749840942237503172545281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10333121256316670896727041 7749840942237503172545281)
              ·
                refine ⟨5812380706678127379408961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7749840942237503172545281 5812380706678127379408961)
                ·
                  refine ⟨4359285530008595534556721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5812380706678127379408961 4359285530008595534556721)
                  ·
                    refine ⟨3269464147506446650917541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4359285530008595534556721 3269464147506446650917541)
                    ·
                      refine ⟨613024527657458747047039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3269464147506446650917541 613024527657458747047039)
                      ·
                        rfl

theorem cell23_1193861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_1193861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193861 prefixEnd_1193861 := by exact prefixLift 1193861
  have htrace : WordTrace (prefixWord ++ tailWord_1193861) baseStart_1193861 baseEnd_1193861 := by
    simpa [prefixWord, tailWord_1193861, baseEnd_1193861] using wordTrace_append hprefix tailTrace_1193861
  have hstable : (prefixWord ++ tailWord_1193861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193861).length < 2 ^ (prefixWord ++ tailWord_1193861).sum := by decide
  have hdescent : baseEnd_1193861 < baseStart_1193861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193881 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_1193881 : Nat := 118140960795 + 1193881 * 2 ^ 59
def prefixEnd_1193881 : Nat := 4983230072969 + 3 ^ 40 * 1193881 * 2
def baseEnd_1193881 : Nat := 613034797270548668796947

theorem tailTrace_1193881 : CollatzResearch.WordTrace tailWord_1193881 prefixEnd_1193881 613034797270548668796947 := by
  unfold tailWord_1193881
  simp only [CollatzResearch.WordTrace]
  refine ⟨43544417387780510486709497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29029611591853673657806331 43544417387780510486709497)
  ·
    refine ⟨32658313040835382865032123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43544417387780510486709497 32658313040835382865032123)
    ·
      refine ⟨48987469561253074297548185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32658313040835382865032123 48987469561253074297548185)
      ·
        refine ⟨36740602170939805723161139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48987469561253074297548185 36740602170939805723161139)
        ·
          refine ⟨55110903256409708584741709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36740602170939805723161139 55110903256409708584741709)
          ·
            refine ⟨20666588721153640719278141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55110903256409708584741709 20666588721153640719278141)
            ·
              refine ⟨7749970770432615269729303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20666588721153640719278141 7749970770432615269729303)
              ·
                refine ⟨11624956155648922904593955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7749970770432615269729303 11624956155648922904593955)
                ·
                  refine ⟨17437434233473384356890933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11624956155648922904593955 17437434233473384356890933)
                  ·
                    refine ⟨1634759459388129783458525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17437434233473384356890933 1634759459388129783458525)
                    ·
                      refine ⟨613034797270548668796947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634759459388129783458525 613034797270548668796947)
                      ·
                        rfl

theorem cell23_1193881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_1193881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193881 prefixEnd_1193881 := by exact prefixLift 1193881
  have htrace : WordTrace (prefixWord ++ tailWord_1193881) baseStart_1193881 baseEnd_1193881 := by
    simpa [prefixWord, tailWord_1193881, baseEnd_1193881] using wordTrace_append hprefix tailTrace_1193881
  have hstable : (prefixWord ++ tailWord_1193881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193881).length < 2 ^ (prefixWord ++ tailWord_1193881).sum := by decide
  have hdescent : baseEnd_1193881 < baseStart_1193881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193882 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_1193882 : Nat := 118140960795 + 1193882 * 2 ^ 59
def prefixEnd_1193882 : Nat := 4983230072969 + 3 ^ 40 * 1193882 * 2
def baseEnd_1193882 : Nat := 613035310751203164884443

theorem tailTrace_1193882 : CollatzResearch.WordTrace tailWord_1193882 prefixEnd_1193882 613035310751203164884443 := by
  unfold tailWord_1193882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10886113465194221914373975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29029635907184591771663933 10886113465194221914373975)
  ·
    refine ⟨16329170197791332871560963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10886113465194221914373975 16329170197791332871560963)
    ·
      refine ⟨24493755296686999307341445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16329170197791332871560963 24493755296686999307341445)
      ·
        refine ⟨4592579118128812370126521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24493755296686999307341445 4592579118128812370126521)
        ·
          refine ⟨3444434338596609277594891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4592579118128812370126521 3444434338596609277594891)
          ·
            refine ⟨5166651507894913916392337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444434338596609277594891 5166651507894913916392337)
            ·
              refine ⟨3874988630921185437294253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166651507894913916392337 3874988630921185437294253)
              ·
                refine ⟨1453120736595444538985345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3874988630921185437294253 1453120736595444538985345)
                ·
                  refine ⟨1089840552446583404239009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1453120736595444538985345 1089840552446583404239009)
                  ·
                    refine ⟨817380414334937553179257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089840552446583404239009 817380414334937553179257)
                    ·
                      refine ⟨613035310751203164884443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817380414334937553179257 613035310751203164884443)
                      ·
                        rfl

theorem cell23_1193882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_1193882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193882 prefixEnd_1193882 := by exact prefixLift 1193882
  have htrace : WordTrace (prefixWord ++ tailWord_1193882) baseStart_1193882 baseEnd_1193882 := by
    simpa [prefixWord, tailWord_1193882, baseEnd_1193882] using wordTrace_append hprefix tailTrace_1193882
  have hstable : (prefixWord ++ tailWord_1193882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193882).length < 2 ^ (prefixWord ++ tailWord_1193882).sum := by decide
  have hdescent : baseEnd_1193882 < baseStart_1193882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193905 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 5]
def baseStart_1193905 : Nat := 118140960795 + 1193905 * 2 ^ 59
def prefixEnd_1193905 : Nat := 4983230072969 + 3 ^ 40 * 1193905 * 2
def baseEnd_1193905 : Nat := 68116346756250730544093

theorem tailTrace_1193905 : CollatzResearch.WordTrace tailWord_1193905 prefixEnd_1193905 68116346756250730544093 := by
  unfold tailWord_1193905
  simp only [CollatzResearch.WordTrace]
  refine ⟨43545292739693562585583169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29030195159795708390388779 43545292739693562585583169)
  ·
    refine ⟨32658969554770171939187377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43545292739693562585583169 32658969554770171939187377)
    ·
      refine ⟨24494227166077628954390533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32658969554770171939187377 24494227166077628954390533)
      ·
        refine ⟨4592667593639555428948225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24494227166077628954390533 4592667593639555428948225)
        ·
          refine ⟨3444500695229666571711169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4592667593639555428948225 3444500695229666571711169)
          ·
            refine ⟨2583375521422249928783377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3444500695229666571711169 2583375521422249928783377)
            ·
              refine ⟨1937531641066687446587533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583375521422249928783377 1937531641066687446587533)
              ·
                refine ⟨726574365400007792470325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1937531641066687446587533 726574365400007792470325)
                ·
                  refine ⟨68116346756250730544093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 726574365400007792470325 68116346756250730544093)
                  ·
                    rfl

theorem cell23_1193905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 5].length) (baseStart_1193905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193905 prefixEnd_1193905 := by exact prefixLift 1193905
  have htrace : WordTrace (prefixWord ++ tailWord_1193905) baseStart_1193905 baseEnd_1193905 := by
    simpa [prefixWord, tailWord_1193905, baseEnd_1193905] using wordTrace_append hprefix tailTrace_1193905
  have hstable : (prefixWord ++ tailWord_1193905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193905).length < 2 ^ (prefixWord ++ tailWord_1193905).sum := by decide
  have hdescent : baseEnd_1193905 < baseStart_1193905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193916 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1193916 : Nat := 118140960795 + 1193916 * 2 ^ 59
def prefixEnd_1193916 : Nat := 4983230072969 + 3 ^ 40 * 1193916 * 2
def baseEnd_1193916 : Nat := 613052769093456031859287

theorem tailTrace_1193916 : CollatzResearch.WordTrace tailWord_1193916 prefixEnd_1193916 613052769093456031859287 := by
  unfold tailWord_1193916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21772846971326855732116801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29030462628435807642822401 21772846971326855732116801)
  ·
    refine ⟨16329635228495141799087601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21772846971326855732116801 16329635228495141799087601)
    ·
      refine ⟨12247226421371356349315701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16329635228495141799087601 12247226421371356349315701)
      ·
        refine ⟨1148177477003564657748347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12247226421371356349315701 1148177477003564657748347)
        ·
          refine ⟨1722266215505346986622521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148177477003564657748347 1722266215505346986622521)
          ·
            refine ⟨1291699661629010239966891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1722266215505346986622521 1291699661629010239966891)
            ·
              refine ⟨1937549492443515359950337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291699661629010239966891 1937549492443515359950337)
              ·
                refine ⟨1453162119332636519962753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937549492443515359950337 1453162119332636519962753)
                ·
                  refine ⟨1089871589499477389972065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1453162119332636519962753 1089871589499477389972065)
                  ·
                    refine ⟨817403692124608042479049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1089871589499477389972065 817403692124608042479049)
                    ·
                      refine ⟨613052769093456031859287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817403692124608042479049 613052769093456031859287)
                      ·
                        rfl

theorem cell23_1193916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1193916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193916 prefixEnd_1193916 := by exact prefixLift 1193916
  have htrace : WordTrace (prefixWord ++ tailWord_1193916) baseStart_1193916 baseEnd_1193916 := by
    simpa [prefixWord, tailWord_1193916, baseEnd_1193916] using wordTrace_append hprefix tailTrace_1193916
  have hstable : (prefixWord ++ tailWord_1193916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193916).length < 2 ^ (prefixWord ++ tailWord_1193916).sum := by decide
  have hdescent : baseEnd_1193916 < baseStart_1193916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193981 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1193981 : Nat := 118140960795 + 1193981 * 2 ^ 59
def prefixEnd_1193981 : Nat := 4983230072969 + 3 ^ 40 * 1193981 * 2
def baseEnd_1193981 : Nat := 613086145335998277546487

theorem tailTrace_1193981 : CollatzResearch.WordTrace tailWord_1193981 prefixEnd_1193981 613086145335998277546487 := by
  unfold tailWord_1193981
  simp only [CollatzResearch.WordTrace]
  refine ⟨43548064687418227565349797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29032043124945485043566531 43548064687418227565349797)
  ·
    refine ⟨8165262128890917668503087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43548064687418227565349797 8165262128890917668503087)
    ·
      refine ⟨12247893193336376502754631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8165262128890917668503087 12247893193336376502754631)
      ·
        refine ⟨18371839790004564754131947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12247893193336376502754631 18371839790004564754131947)
        ·
          refine ⟨27557759685006847131197921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18371839790004564754131947 27557759685006847131197921)
          ·
            refine ⟨20668319763755135348398441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27557759685006847131197921 20668319763755135348398441)
            ·
              refine ⟨15501239822816351511298831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20668319763755135348398441 15501239822816351511298831)
              ·
                refine ⟨23251859734224527266948247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15501239822816351511298831 23251859734224527266948247)
                ·
                  refine ⟨34877789601336790900422371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23251859734224527266948247 34877789601336790900422371)
                  ·
                    refine ⟨52316684402005186350633557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34877789601336790900422371 52316684402005186350633557)
                    ·
                      refine ⟨613086145335998277546487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52316684402005186350633557 613086145335998277546487)
                      ·
                        rfl

theorem cell23_1193981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1193981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193981 prefixEnd_1193981 := by exact prefixLift 1193981
  have htrace : WordTrace (prefixWord ++ tailWord_1193981) baseStart_1193981 baseEnd_1193981 := by
    simpa [prefixWord, tailWord_1193981, baseEnd_1193981] using wordTrace_append hprefix tailTrace_1193981
  have hstable : (prefixWord ++ tailWord_1193981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193981).length < 2 ^ (prefixWord ++ tailWord_1193981).sum := by decide
  have hdescent : baseEnd_1193981 < baseStart_1193981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193982 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1193982 : Nat := 118140960795 + 1193982 * 2 ^ 59
def prefixEnd_1193982 : Nat := 4983230072969 + 3 ^ 40 * 1193982 * 2
def baseEnd_1193982 : Nat := 204362219605550924544661

theorem tailTrace_1193982 : CollatzResearch.WordTrace tailWord_1193982 prefixEnd_1193982 204362219605550924544661 := by
  unfold tailWord_1193982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443512645051825592017025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29032067440276403157424133 5443512645051825592017025)
  ·
    refine ⟨4082634483788869194012769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5443512645051825592017025 4082634483788869194012769)
    ·
      refine ⟨3061975862841651895509577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4082634483788869194012769 3061975862841651895509577)
      ·
        refine ⟨2296481897131238921632183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061975862841651895509577 2296481897131238921632183)
        ·
          refine ⟨3444722845696858382448275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296481897131238921632183 3444722845696858382448275)
          ·
            refine ⟨5167084268545287573672413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444722845696858382448275 5167084268545287573672413)
            ·
              refine ⟨1937656600704482840127155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5167084268545287573672413 1937656600704482840127155)
              ·
                refine ⟨2906484901056724260190733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937656600704482840127155 2906484901056724260190733)
                ·
                  refine ⟨1089931837896271597571525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2906484901056724260190733 1089931837896271597571525)
                  ·
                    refine ⟨204362219605550924544661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089931837896271597571525 204362219605550924544661)
                    ·
                      rfl

theorem cell23_1193982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1193982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1193982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1193982 prefixEnd_1193982 := by exact prefixLift 1193982
  have htrace : WordTrace (prefixWord ++ tailWord_1193982) baseStart_1193982 baseEnd_1193982 := by
    simpa [prefixWord, tailWord_1193982, baseEnd_1193982] using wordTrace_append hprefix tailTrace_1193982
  have hstable : (prefixWord ++ tailWord_1193982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193982).length < 2 ^ (prefixWord ++ tailWord_1193982).sum := by decide
  have hdescent : baseEnd_1193982 < baseStart_1193982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194008 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_1194008 : Nat := 118140960795 + 1194008 * 2 ^ 59
def prefixEnd_1194008 : Nat := 4983230072969 + 3 ^ 40 * 1194008 * 2
def baseEnd_1194008 : Nat := 204366669771223223969621

theorem tailTrace_1194008 : CollatzResearch.WordTrace tailWord_1194008 prefixEnd_1194008 204366669771223223969621 := by
  unfold tailWord_1194008
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774524729160205588291339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29032699638880274117721785 21774524729160205588291339)
  ·
    refine ⟨32661787093740308382437009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21774524729160205588291339 32661787093740308382437009)
    ·
      refine ⟨24496340320305231286827757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32661787093740308382437009 24496340320305231286827757)
      ·
        refine ⟨9186127620114461732560409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24496340320305231286827757 9186127620114461732560409)
        ·
          refine ⟨6889595715085846299420307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9186127620114461732560409 6889595715085846299420307)
          ·
            refine ⟨10334393572628769449130461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889595715085846299420307 10334393572628769449130461)
            ·
              refine ⟨3875397589735788543423923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10334393572628769449130461 3875397589735788543423923)
              ·
                refine ⟨5813096384603682815135885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875397589735788543423923 5813096384603682815135885)
                ·
                  refine ⟨2179911144226381055675957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5813096384603682815135885 2179911144226381055675957)
                  ·
                    refine ⟨204366669771223223969621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2179911144226381055675957 204366669771223223969621)
                    ·
                      rfl

theorem cell23_1194008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_1194008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194008 prefixEnd_1194008 := by exact prefixLift 1194008
  have htrace : WordTrace (prefixWord ++ tailWord_1194008) baseStart_1194008 baseEnd_1194008 := by
    simpa [prefixWord, tailWord_1194008, baseEnd_1194008] using wordTrace_append hprefix tailTrace_1194008
  have hstable : (prefixWord ++ tailWord_1194008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194008).length < 2 ^ (prefixWord ++ tailWord_1194008).sum := by decide
  have hdescent : baseEnd_1194008 < baseStart_1194008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194039 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 1, 1, 3]
def baseStart_1194039 : Nat := 118140960795 + 1194039 * 2 ^ 59
def prefixEnd_1194039 : Nat := 4983230072969 + 3 ^ 40 * 1194039 * 2
def baseEnd_1194039 : Nat := 613115927213959050621221

theorem tailTrace_1194039 : CollatzResearch.WordTrace tailWord_1194039 prefixEnd_1194039 613115927213959050621221 := by
  unfold tailWord_1194039
  simp only [CollatzResearch.WordTrace]
  refine ⟨43550180121208103470961171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29033453414138735647307447 43550180121208103470961171)
  ·
    refine ⟨65325270181812155206441757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43550180121208103470961171 65325270181812155206441757)
    ·
      refine ⟨24496976318179558202415659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65325270181812155206441757 24496976318179558202415659)
      ·
        refine ⟨36745464477269337303623489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24496976318179558202415659 36745464477269337303623489)
        ·
          refine ⟨27559098357952002977717617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36745464477269337303623489 27559098357952002977717617)
          ·
            refine ⟨20669323768464002233288213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27559098357952002977717617 20669323768464002233288213)
            ·
              refine ⟨968874551646750104685385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20669323768464002233288213 968874551646750104685385)
              ·
                refine ⟨726655913735062578514039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968874551646750104685385 726655913735062578514039)
                ·
                  refine ⟨1089983870602593867771059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726655913735062578514039 1089983870602593867771059)
                  ·
                    refine ⟨1634975805903890801656589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1089983870602593867771059 1634975805903890801656589)
                    ·
                      refine ⟨613115927213959050621221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1634975805903890801656589 613115927213959050621221)
                      ·
                        rfl

theorem cell23_1194039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_1194039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194039 prefixEnd_1194039 := by exact prefixLift 1194039
  have htrace : WordTrace (prefixWord ++ tailWord_1194039) baseStart_1194039 baseEnd_1194039 := by
    simpa [prefixWord, tailWord_1194039, baseEnd_1194039] using wordTrace_append hprefix tailTrace_1194039
  have hstable : (prefixWord ++ tailWord_1194039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194039).length < 2 ^ (prefixWord ++ tailWord_1194039).sum := by decide
  have hdescent : baseEnd_1194039 < baseStart_1194039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194051 : List Nat := [1, 1, 1, 3, 1, 2, 2, 12]
def baseStart_1194051 : Nat := 118140960795 + 1194051 * 2 ^ 59
def prefixEnd_1194051 : Nat := 4983230072969 + 3 ^ 40 * 1194051 * 2
def baseEnd_1194051 : Nat := 22708225517844926061895

theorem tailTrace_1194051 : CollatzResearch.WordTrace tailWord_1194051 prefixEnd_1194051 22708225517844926061895 := by
  unfold tailWord_1194051
  simp only [CollatzResearch.WordTrace]
  refine ⟨43550617797164629520398007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29033745198109753013598671 43550617797164629520398007)
  ·
    refine ⟨65325926695746944280597011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43550617797164629520398007 65325926695746944280597011)
    ·
      refine ⟨97988890043620416420895517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65325926695746944280597011 97988890043620416420895517)
      ·
        refine ⟨36745833766357656157835819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97988890043620416420895517 36745833766357656157835819)
        ·
          refine ⟨55118750649536484236753729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36745833766357656157835819 55118750649536484236753729)
          ·
            refine ⟨41339062987152363177565297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55118750649536484236753729 41339062987152363177565297)
            ·
              refine ⟨31004297240364272383173973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41339062987152363177565297 31004297240364272383173973)
              ·
                refine ⟨22708225517844926061895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 31004297240364272383173973 22708225517844926061895)
                ·
                  rfl

theorem cell23_1194051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 12].length) (baseStart_1194051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194051 prefixEnd_1194051 := by exact prefixLift 1194051
  have htrace : WordTrace (prefixWord ++ tailWord_1194051) baseStart_1194051 baseEnd_1194051 := by
    simpa [prefixWord, tailWord_1194051, baseEnd_1194051] using wordTrace_append hprefix tailTrace_1194051
  have hstable : (prefixWord ++ tailWord_1194051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194051).length < 2 ^ (prefixWord ++ tailWord_1194051).sum := by decide
  have hdescent : baseEnd_1194051 < baseStart_1194051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194055 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 2, 4]
def baseStart_1194055 : Nat := 118140960795 + 1194055 * 2 ^ 59
def prefixEnd_1194055 : Nat := 4983230072969 + 3 ^ 40 * 1194055 * 2
def baseEnd_1194055 : Nat := 204374714301476996007049

theorem tailTrace_1194055 : CollatzResearch.WordTrace tailWord_1194055 prefixEnd_1194055 204374714301476996007049 := by
  unfold tailWord_1194055
  simp only [CollatzResearch.WordTrace]
  refine ⟨43550763689150138203543619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29033842459433425469029079 43550763689150138203543619)
  ·
    refine ⟨65326145533725207305315429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43550763689150138203543619 65326145533725207305315429)
    ·
      refine ⟨12248652287573476369746643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65326145533725207305315429 12248652287573476369746643)
      ·
        refine ⟨18372978431360214554619965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12248652287573476369746643 18372978431360214554619965)
        ·
          refine ⟨6889866911760080457982487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18372978431360214554619965 6889866911760080457982487)
          ·
            refine ⟨10334800367640120686973731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6889866911760080457982487 10334800367640120686973731)
            ·
              refine ⟨15502200551460181030460597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334800367640120686973731 15502200551460181030460597)
              ·
                refine ⟨1453331301699391971605681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15502200551460181030460597 1453331301699391971605681)
                ·
                  refine ⟨1089998476274543978704261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1453331301699391971605681 1089998476274543978704261)
                  ·
                    refine ⟨204374714301476996007049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089998476274543978704261 204374714301476996007049)
                    ·
                      rfl

theorem cell23_1194055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_1194055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194055 prefixEnd_1194055 := by exact prefixLift 1194055
  have htrace : WordTrace (prefixWord ++ tailWord_1194055) baseStart_1194055 baseEnd_1194055 := by
    simpa [prefixWord, tailWord_1194055, baseEnd_1194055] using wordTrace_append hprefix tailTrace_1194055
  have hstable : (prefixWord ++ tailWord_1194055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194055).length < 2 ^ (prefixWord ++ tailWord_1194055).sum := by decide
  have hdescent : baseEnd_1194055 < baseStart_1194055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194062 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2]
def baseStart_1194062 : Nat := 118140960795 + 1194062 * 2 ^ 59
def prefixEnd_1194062 : Nat := 4983230072969 + 3 ^ 40 * 1194062 * 2
def baseEnd_1194062 : Nat := 613127737269012460633615

theorem tailTrace_1194062 : CollatzResearch.WordTrace tailWord_1194062 prefixEnd_1194062 613127737269012460633615 := by
  unfold tailWord_1194062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443877375015597299881055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29034012666749852266032293 5443877375015597299881055)
  ·
    refine ⟨8165816062523395949821583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443877375015597299881055 8165816062523395949821583)
    ·
      refine ⟨12248724093785093924732375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8165816062523395949821583 12248724093785093924732375)
      ·
        refine ⟨18373086140677640887098563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12248724093785093924732375 18373086140677640887098563)
        ·
          refine ⟨27559629211016461330647845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18373086140677640887098563 27559629211016461330647845)
          ·
            refine ⟨5167430477065586499496471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27559629211016461330647845 5167430477065586499496471)
            ·
              refine ⟨7751145715598379749244707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167430477065586499496471 7751145715598379749244707)
              ·
                refine ⟨11626718573397569623867061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751145715598379749244707 11626718573397569623867061)
                ·
                  refine ⟨1090004866256022152237537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11626718573397569623867061 1090004866256022152237537)
                  ·
                    refine ⟨817503649692016614178153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090004866256022152237537 817503649692016614178153)
                    ·
                      refine ⟨613127737269012460633615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817503649692016614178153 613127737269012460633615)
                      ·
                        rfl

theorem cell23_1194062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_1194062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194062 prefixEnd_1194062 := by exact prefixLift 1194062
  have htrace : WordTrace (prefixWord ++ tailWord_1194062) baseStart_1194062 baseEnd_1194062 := by
    simpa [prefixWord, tailWord_1194062, baseEnd_1194062] using wordTrace_append hprefix tailTrace_1194062
  have hstable : (prefixWord ++ tailWord_1194062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194062).length < 2 ^ (prefixWord ++ tailWord_1194062).sum := by decide
  have hdescent : baseEnd_1194062 < baseStart_1194062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194065 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_1194065 : Nat := 118140960795 + 1194065 * 2 ^ 59
def prefixEnd_1194065 : Nat := 4983230072969 + 3 ^ 40 * 1194065 * 2
def baseEnd_1194065 : Nat := 613129277710975948896101

theorem tailTrace_1194065 : CollatzResearch.WordTrace tailWord_1194065 prefixEnd_1194065 613129277710975948896101 := by
  unfold tailWord_1194065
  simp only [CollatzResearch.WordTrace]
  refine ⟨43551128419113909911407649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29034085612742606607605099 43551128419113909911407649)
  ·
    refine ⟨32663346314335432433555737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43551128419113909911407649 32663346314335432433555737)
    ·
      refine ⟨24497509735751574325166803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32663346314335432433555737 24497509735751574325166803)
      ·
        refine ⟨36746264603627361487750205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24497509735751574325166803 36746264603627361487750205)
        ·
          refine ⟨13779849226360260557906327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36746264603627361487750205 13779849226360260557906327)
          ·
            refine ⟨20669773839540390836859491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13779849226360260557906327 20669773839540390836859491)
            ·
              refine ⟨31004660759310586255289237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20669773839540390836859491 31004660759310586255289237)
              ·
                refine ⟨1453343473092683730716683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31004660759310586255289237 1453343473092683730716683)
                ·
                  refine ⟨2180015209639025596075025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453343473092683730716683 2180015209639025596075025)
                  ·
                    refine ⟨1635011407229269197056269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180015209639025596075025 1635011407229269197056269)
                    ·
                      refine ⟨613129277710975948896101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1635011407229269197056269 613129277710975948896101)
                      ·
                        rfl

theorem cell23_1194065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_1194065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194065 prefixEnd_1194065 := by exact prefixLift 1194065
  have htrace : WordTrace (prefixWord ++ tailWord_1194065) baseStart_1194065 baseEnd_1194065 := by
    simpa [prefixWord, tailWord_1194065, baseEnd_1194065] using wordTrace_append hprefix tailTrace_1194065
  have hstable : (prefixWord ++ tailWord_1194065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194065).length < 2 ^ (prefixWord ++ tailWord_1194065).sum := by decide
  have hdescent : baseEnd_1194065 < baseStart_1194065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194066 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_1194066 : Nat := 118140960795 + 1194066 * 2 ^ 59
def prefixEnd_1194066 : Nat := 4983230072969 + 3 ^ 40 * 1194066 * 2
def baseEnd_1194066 : Nat := 613129791191630444983597

theorem tailTrace_1194066 : CollatzResearch.WordTrace tailWord_1194066 prefixEnd_1194066 613129791191630444983597 := by
  unfold tailWord_1194066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10887791223027571770548513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29034109928073524721462701 10887791223027571770548513)
  ·
    refine ⟨8165843417270678827911385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10887791223027571770548513 8165843417270678827911385)
    ·
      refine ⟨6124382562953009120933539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165843417270678827911385 6124382562953009120933539)
      ·
        refine ⟨9186573844429513681400309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124382562953009120933539 9186573844429513681400309)
        ·
          refine ⟨861241297915266907631279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9186573844429513681400309 861241297915266907631279)
          ·
            refine ⟨1291861946872900361446919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861241297915266907631279 1291861946872900361446919)
            ·
              refine ⟨1937792920309350542170379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291861946872900361446919 1937792920309350542170379)
              ·
                refine ⟨2906689380464025813255569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937792920309350542170379 2906689380464025813255569)
                ·
                  refine ⟨2180017035348019359941677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906689380464025813255569 2180017035348019359941677)
                  ·
                    refine ⟨817506388255507259978129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2180017035348019359941677 817506388255507259978129)
                    ·
                      refine ⟨613129791191630444983597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817506388255507259978129 613129791191630444983597)
                      ·
                        rfl

theorem cell23_1194066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_1194066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194066 prefixEnd_1194066 := by exact prefixLift 1194066
  have htrace : WordTrace (prefixWord ++ tailWord_1194066) baseStart_1194066 baseEnd_1194066 := by
    simpa [prefixWord, tailWord_1194066, baseEnd_1194066] using wordTrace_append hprefix tailTrace_1194066
  have hstable : (prefixWord ++ tailWord_1194066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194066).length < 2 ^ (prefixWord ++ tailWord_1194066).sum := by decide
  have hdescent : baseEnd_1194066 < baseStart_1194066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194169 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1194169 : Nat := 118140960795 + 1194169 * 2 ^ 59
def prefixEnd_1194169 : Nat := 4983230072969 + 3 ^ 40 * 1194169 * 2
def baseEnd_1194169 : Nat := 613182679699043541995623

theorem tailTrace_1194169 : CollatzResearch.WordTrace tailWord_1194169 prefixEnd_1194169 613182679699043541995623 := by
  unfold tailWord_1194169
  simp only [CollatzResearch.WordTrace]
  refine ⟨43554921610737135673193561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29036614407158090448795707 43554921610737135673193561)
  ·
    refine ⟨32666191208052851754895171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43554921610737135673193561 32666191208052851754895171)
    ·
      refine ⟨48999286812079277632342757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32666191208052851754895171 48999286812079277632342757)
      ·
        refine ⟨9187366277264864556064267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48999286812079277632342757 9187366277264864556064267)
        ·
          refine ⟨13781049415897296834096401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9187366277264864556064267 13781049415897296834096401)
          ·
            refine ⟨10335787061922972625572301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13781049415897296834096401 10335787061922972625572301)
            ·
              refine ⟨3875920148221114734589613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10335787061922972625572301 3875920148221114734589613)
              ·
                refine ⟨1453470055582918025471105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3875920148221114734589613 1453470055582918025471105)
                ·
                  refine ⟨1090102541687188519103329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1453470055582918025471105 1090102541687188519103329)
                  ·
                    refine ⟨817576906265391389327497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090102541687188519103329 817576906265391389327497)
                    ·
                      refine ⟨613182679699043541995623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817576906265391389327497 613182679699043541995623)
                      ·
                        rfl

theorem cell23_1194169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1194169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194169 prefixEnd_1194169 := by exact prefixLift 1194169
  have htrace : WordTrace (prefixWord ++ tailWord_1194169) baseStart_1194169 baseEnd_1194169 := by
    simpa [prefixWord, tailWord_1194169, baseEnd_1194169] using wordTrace_append hprefix tailTrace_1194169
  have hstable : (prefixWord ++ tailWord_1194169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194169).length < 2 ^ (prefixWord ++ tailWord_1194169).sum := by decide
  have hdescent : baseEnd_1194169 < baseStart_1194169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194195 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 3, 7, 2]
def baseStart_1194195 : Nat := 118140960795 + 1194195 * 2 ^ 59
def prefixEnd_1194195 : Nat := 4983230072969 + 3 ^ 40 * 1194195 * 2
def baseEnd_1194195 : Nat := 613196030196060440270503

theorem tailTrace_1194195 : CollatzResearch.WordTrace tailWord_1194195 prefixEnd_1194195 613196030196060440270503 := by
  unfold tailWord_1194195
  simp only [CollatzResearch.WordTrace]
  refine ⟨43555869908642942113640039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29037246605761961409093359 43555869908642942113640039)
  ·
    refine ⟨65333804862964413170460059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43555869908642942113640039 65333804862964413170460059)
    ·
      refine ⟨98000707294446619755690089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65333804862964413170460059 98000707294446619755690089)
      ·
        refine ⟨73500530470834964816767567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98000707294446619755690089 73500530470834964816767567)
        ·
          refine ⟨110250795706252447225151351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73500530470834964816767567 110250795706252447225151351)
          ·
            refine ⟨165376193559378670837727027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110250795706252447225151351 165376193559378670837727027)
            ·
              refine ⟨248064290339068006256590541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165376193559378670837727027 248064290339068006256590541)
              ·
                refine ⟨93024108877150502346221453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248064290339068006256590541 93024108877150502346221453)
                ·
                  refine ⟨34884040828931438379833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93024108877150502346221453 34884040828931438379833045)
                  ·
                    refine ⟨817594706928080587027337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34884040828931438379833045 817594706928080587027337)
                    ·
                      refine ⟨613196030196060440270503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817594706928080587027337 613196030196060440270503)
                      ·
                        rfl

theorem cell23_1194195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7, 2].length) (baseStart_1194195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194195 prefixEnd_1194195 := by exact prefixLift 1194195
  have htrace : WordTrace (prefixWord ++ tailWord_1194195) baseStart_1194195 baseEnd_1194195 := by
    simpa [prefixWord, tailWord_1194195, baseEnd_1194195] using wordTrace_append hprefix tailTrace_1194195
  have hstable : (prefixWord ++ tailWord_1194195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194195).length < 2 ^ (prefixWord ++ tailWord_1194195).sum := by decide
  have hdescent : baseEnd_1194195 < baseStart_1194195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194225 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_1194225 : Nat := 118140960795 + 1194225 * 2 ^ 59
def prefixEnd_1194225 : Nat := 4983230072969 + 3 ^ 40 * 1194225 * 2
def baseEnd_1194225 : Nat := 613211434615695322895365

theorem tailTrace_1194225 : CollatzResearch.WordTrace tailWord_1194225 prefixEnd_1194225 613211434615695322895365 := by
  unfold tailWord_1194225
  simp only [CollatzResearch.WordTrace]
  refine ⟨43556964098534257237232129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29037976065689504824821419 43556964098534257237232129)
  ·
    refine ⟨32667723073900692927924097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43556964098534257237232129 32667723073900692927924097)
    ·
      refine ⟨24500792305425519695943073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32667723073900692927924097 24500792305425519695943073)
      ·
        refine ⟨18375594229069139771957305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24500792305425519695943073 18375594229069139771957305)
        ·
          refine ⟨13781695671801854828967979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18375594229069139771957305 13781695671801854828967979)
          ·
            refine ⟨20672543507702782243451969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13781695671801854828967979 20672543507702782243451969)
            ·
              refine ⟨15504407630777086682588977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20672543507702782243451969 15504407630777086682588977)
              ·
                refine ⟨11628305723082815011941733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15504407630777086682588977 11628305723082815011941733)
                ·
                  refine ⟨2180307323078027814739075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11628305723082815011941733 2180307323078027814739075)
                  ·
                    refine ⟨3270460984617041722108613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2180307323078027814739075 3270460984617041722108613)
                    ·
                      refine ⟨613211434615695322895365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3270460984617041722108613 613211434615695322895365)
                      ·
                        rfl

theorem cell23_1194225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_1194225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194225 prefixEnd_1194225 := by exact prefixLift 1194225
  have htrace : WordTrace (prefixWord ++ tailWord_1194225) baseStart_1194225 baseEnd_1194225 := by
    simpa [prefixWord, tailWord_1194225, baseEnd_1194225] using wordTrace_append hprefix tailTrace_1194225
  have hstable : (prefixWord ++ tailWord_1194225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194225).length < 2 ^ (prefixWord ++ tailWord_1194225).sum := by decide
  have hdescent : baseEnd_1194225 < baseStart_1194225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194295 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 3, 5]
def baseStart_1194295 : Nat := 118140960795 + 1194295 * 2 ^ 59
def prefixEnd_1194295 : Nat := 4983230072969 + 3 ^ 40 * 1194295 * 2
def baseEnd_1194295 : Nat := 204415792753836683006681

theorem tailTrace_1194295 : CollatzResearch.WordTrace tailWord_1194295 prefixEnd_1194295 204415792753836683006681 := by
  unfold tailWord_1194295
  simp only [CollatzResearch.WordTrace]
  refine ⟨43559517208280659192280339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29039678138853772794853559 43559517208280659192280339)
  ·
    refine ⟨65339275812420988788420509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43559517208280659192280339 65339275812420988788420509)
    ·
      refine ⟨24502228429657870795657691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65339275812420988788420509 24502228429657870795657691)
      ·
        refine ⟨36753342644486806193486537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24502228429657870795657691 36753342644486806193486537)
        ·
          refine ⟨27565006983365104645114903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36753342644486806193486537 27565006983365104645114903)
          ·
            refine ⟨41347510475047656967672355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27565006983365104645114903 41347510475047656967672355)
            ·
              refine ⟨62021265712571485451508533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41347510475047656967672355 62021265712571485451508533)
              ·
                refine ⟨5814493660553576761078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62021265712571485451508533 5814493660553576761078925)
                ·
                  refine ⟨2180435122707591285404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5814493660553576761078925 2180435122707591285404597)
                  ·
                    refine ⟨204415792753836683006681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2180435122707591285404597 204415792753836683006681)
                    ·
                      rfl

theorem cell23_1194295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_1194295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194295 prefixEnd_1194295 := by exact prefixLift 1194295
  have htrace : WordTrace (prefixWord ++ tailWord_1194295) baseStart_1194295 baseEnd_1194295 := by
    simpa [prefixWord, tailWord_1194295, baseEnd_1194295] using wordTrace_append hprefix tailTrace_1194295
  have hstable : (prefixWord ++ tailWord_1194295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194295).length < 2 ^ (prefixWord ++ tailWord_1194295).sum := by decide
  have hdescent : baseEnd_1194295 < baseStart_1194295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194312 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1194312 : Nat := 118140960795 + 1194312 * 2 ^ 59
def prefixEnd_1194312 : Nat := 4983230072969 + 3 ^ 40 * 1194312 * 2
def baseEnd_1194312 : Nat := 204418702477545494169155

theorem tailTrace_1194312 : CollatzResearch.WordTrace tailWord_1194312 prefixEnd_1194312 204418702477545494169155 := by
  unfold tailWord_1194312
  simp only [CollatzResearch.WordTrace]
  refine ⟨21780068624609535547824595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29040091499479380730432793 21780068624609535547824595)
  ·
    refine ⟨32670102936914303321736893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21780068624609535547824595 32670102936914303321736893)
    ·
      refine ⟨12251288601342863745651335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32670102936914303321736893 12251288601342863745651335)
      ·
        refine ⟨18376932902014295618477003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12251288601342863745651335 18376932902014295618477003)
        ·
          refine ⟨27565399353021443427715505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18376932902014295618477003 27565399353021443427715505)
          ·
            refine ⟨20674049514766082570786629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27565399353021443427715505 20674049514766082570786629)
            ·
              refine ⟨3876384284018640482022493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20674049514766082570786629 3876384284018640482022493)
              ·
                refine ⟨1453644106506990180758435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3876384284018640482022493 1453644106506990180758435)
                ·
                  refine ⟨2180466159760485271137653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453644106506990180758435 2180466159760485271137653)
                  ·
                    refine ⟨204418702477545494169155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2180466159760485271137653 204418702477545494169155)
                    ·
                      rfl

theorem cell23_1194312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1194312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194312 prefixEnd_1194312 := by exact prefixLift 1194312
  have htrace : WordTrace (prefixWord ++ tailWord_1194312) baseStart_1194312 baseEnd_1194312 := by
    simpa [prefixWord, tailWord_1194312, baseEnd_1194312] using wordTrace_append hprefix tailTrace_1194312
  have hstable : (prefixWord ++ tailWord_1194312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194312).length < 2 ^ (prefixWord ++ tailWord_1194312).sum := by decide
  have hdescent : baseEnd_1194312 < baseStart_1194312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194345 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_1194345 : Nat := 118140960795 + 1194345 * 2 ^ 59
def prefixEnd_1194345 : Nat := 4983230072969 + 3 ^ 40 * 1194345 * 2
def baseEnd_1194345 : Nat := 613273052294234853394813

theorem tailTrace_1194345 : CollatzResearch.WordTrace tailWord_1194345 prefixEnd_1194345 613273052294234853394813 := by
  unfold tailWord_1194345
  simp only [CollatzResearch.WordTrace]
  refine ⟨43561340858099517731600489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29040893905399678487733659 43561340858099517731600489)
  ·
    refine ⟨32671005643574638298700367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43561340858099517731600489 32671005643574638298700367)
    ·
      refine ⟨49006508465361957448050551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32671005643574638298700367 49006508465361957448050551)
      ·
        refine ⟨73509762698042936172075827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49006508465361957448050551 73509762698042936172075827)
        ·
          refine ⟨110264644047064404258113741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73509762698042936172075827 110264644047064404258113741)
          ·
            refine ⟨41349241517649151596792653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110264644047064404258113741 41349241517649151596792653)
            ·
              refine ⟨15505965569118431848797245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41349241517649151596792653 15505965569118431848797245)
              ·
                refine ⟨5814737088419411943298967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15505965569118431848797245 5814737088419411943298967)
                ·
                  refine ⟨8722105632629117914948451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5814737088419411943298967 8722105632629117914948451)
                  ·
                    refine ⟨13083158448943676872422677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8722105632629117914948451 13083158448943676872422677)
                    ·
                      refine ⟨613273052294234853394813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13083158448943676872422677 613273052294234853394813)
                      ·
                        rfl

theorem cell23_1194345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_1194345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194345 prefixEnd_1194345 := by exact prefixLift 1194345
  have htrace : WordTrace (prefixWord ++ tailWord_1194345) baseStart_1194345 baseEnd_1194345 := by
    simpa [prefixWord, tailWord_1194345, baseEnd_1194345] using wordTrace_append hprefix tailTrace_1194345
  have hstable : (prefixWord ++ tailWord_1194345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194345).length < 2 ^ (prefixWord ++ tailWord_1194345).sum := by decide
  have hdescent : baseEnd_1194345 < baseStart_1194345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194346 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1194346 : Nat := 118140960795 + 1194346 * 2 ^ 59
def prefixEnd_1194346 : Nat := 4983230072969 + 3 ^ 40 * 1194346 * 2
def baseEnd_1194346 : Nat := 204424521924963116494103

theorem tailTrace_1194346 : CollatzResearch.WordTrace tailWord_1194346 prefixEnd_1194346 204424521924963116494103 := by
  unfold tailWord_1194346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10890344332773973725596723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29040918220730596601591261 10890344332773973725596723)
  ·
    refine ⟨16335516499160960588395085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10890344332773973725596723 16335516499160960588395085)
    ·
      refine ⟨6125818687185360220648157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16335516499160960588395085 6125818687185360220648157)
      ·
        refine ⟨2297182007694510082743059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6125818687185360220648157 2297182007694510082743059)
        ·
          refine ⟨3445773011541765124114589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2297182007694510082743059 3445773011541765124114589)
          ·
            refine ⟨1292164879328161921542971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3445773011541765124114589 1292164879328161921542971)
            ·
              refine ⟨1938247318992242882314457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292164879328161921542971 1938247318992242882314457)
              ·
                refine ⟨1453685489244182161735843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1938247318992242882314457 1453685489244182161735843)
                ·
                  refine ⟨2180528233866273242603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453685489244182161735843 2180528233866273242603765)
                  ·
                    refine ⟨204424521924963116494103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2180528233866273242603765 204424521924963116494103)
                    ·
                      rfl

theorem cell23_1194346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1194346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194346 prefixEnd_1194346 := by exact prefixLift 1194346
  have htrace : WordTrace (prefixWord ++ tailWord_1194346) baseStart_1194346 baseEnd_1194346 := by
    simpa [prefixWord, tailWord_1194346, baseEnd_1194346] using wordTrace_append hprefix tailTrace_1194346
  have hstable : (prefixWord ++ tailWord_1194346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194346).length < 2 ^ (prefixWord ++ tailWord_1194346).sum := by decide
  have hdescent : baseEnd_1194346 < baseStart_1194346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194369 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1194369 : Nat := 118140960795 + 1194369 * 2 ^ 59
def prefixEnd_1194369 : Nat := 4983230072969 + 3 ^ 40 * 1194369 * 2
def baseEnd_1194369 : Nat := 613285375829942759494703

theorem tailTrace_1194369 : CollatzResearch.WordTrace tailWord_1194369 prefixEnd_1194369 613285375829942759494703 := by
  unfold tailWord_1194369
  simp only [CollatzResearch.WordTrace]
  refine ⟨43562216210012569830474161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29041477473341713220316107 43562216210012569830474161)
  ·
    refine ⟨32671662157509427372855621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43562216210012569830474161 32671662157509427372855621)
    ·
      refine ⟨6125936654533017632410429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32671662157509427372855621 6125936654533017632410429)
      ·
        refine ⟨2297226245449881612153911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6125936654533017632410429 2297226245449881612153911)
        ·
          refine ⟨3445839368174822418230867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2297226245449881612153911 3445839368174822418230867)
          ·
            refine ⟨5168759052262233627346301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445839368174822418230867 5168759052262233627346301)
            ·
              refine ⟨1938284644598337610254863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5168759052262233627346301 1938284644598337610254863)
              ·
                refine ⟨2907426966897506415382295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938284644598337610254863 2907426966897506415382295)
                ·
                  refine ⟨4361140450346259623073443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907426966897506415382295 4361140450346259623073443)
                  ·
                    refine ⟨6541710675519389434610165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4361140450346259623073443 6541710675519389434610165)
                    ·
                      refine ⟨613285375829942759494703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6541710675519389434610165 613285375829942759494703)
                      ·
                        rfl

theorem cell23_1194369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1194369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194369 prefixEnd_1194369 := by exact prefixLift 1194369
  have htrace : WordTrace (prefixWord ++ tailWord_1194369) baseStart_1194369 baseEnd_1194369 := by
    simpa [prefixWord, tailWord_1194369, baseEnd_1194369] using wordTrace_append hprefix tailTrace_1194369
  have hstable : (prefixWord ++ tailWord_1194369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194369).length < 2 ^ (prefixWord ++ tailWord_1194369).sum := by decide
  have hdescent : baseEnd_1194369 < baseStart_1194369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194399 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1194399 : Nat := 118140960795 + 1194399 * 2 ^ 59
def prefixEnd_1194399 : Nat := 4983230072969 + 3 ^ 40 * 1194399 * 2
def baseEnd_1194399 : Nat := 613300780249577642119565

theorem tailTrace_1194399 : CollatzResearch.WordTrace tailWord_1194399 prefixEnd_1194399 613300780249577642119565 := by
  unfold tailWord_1194399
  simp only [CollatzResearch.WordTrace]
  refine ⟨43563310399903884954066251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29042206933269256636044167 43563310399903884954066251)
  ·
    refine ⟨65344965599855827431099377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43563310399903884954066251 65344965599855827431099377)
    ·
      refine ⟨49008724199891870573324533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65344965599855827431099377 49008724199891870573324533)
      ·
        refine ⟨4594567893739862866249175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49008724199891870573324533 4594567893739862866249175)
        ·
          refine ⟨6891851840609794299373763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594567893739862866249175 6891851840609794299373763)
          ·
            refine ⟨10337777760914691449060645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6891851840609794299373763 10337777760914691449060645)
            ·
              refine ⟨1938333330171504646698871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10337777760914691449060645 1938333330171504646698871)
              ·
                refine ⟨2907499995257256970048307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938333330171504646698871 2907499995257256970048307)
                ·
                  refine ⟨4361249992885885455072461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907499995257256970048307 4361249992885885455072461)
                  ·
                    refine ⟨1635468747332207045652173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4361249992885885455072461 1635468747332207045652173)
                    ·
                      refine ⟨613300780249577642119565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1635468747332207045652173 613300780249577642119565)
                      ·
                        rfl

theorem cell23_1194399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1194399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194399 prefixEnd_1194399 := by exact prefixLift 1194399
  have htrace : WordTrace (prefixWord ++ tailWord_1194399) baseStart_1194399 baseEnd_1194399 := by
    simpa [prefixWord, tailWord_1194399, baseEnd_1194399] using wordTrace_append hprefix tailTrace_1194399
  have hstable : (prefixWord ++ tailWord_1194399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194399).length < 2 ^ (prefixWord ++ tailWord_1194399).sum := by decide
  have hdescent : baseEnd_1194399 < baseStart_1194399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194402 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1194402 : Nat := 118140960795 + 1194402 * 2 ^ 59
def prefixEnd_1194402 : Nat := 4983230072969 + 3 ^ 40 * 1194402 * 2
def baseEnd_1194402 : Nat := 204434106897180376794017

theorem tailTrace_1194402 : CollatzResearch.WordTrace tailWord_1194402 prefixEnd_1194402 204434106897180376794017 := by
  unfold tailWord_1194402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10890854954723254116606365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29042279879262010977616973 10890854954723254116606365)
  ·
    refine ⟨4084070608021220293727387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10890854954723254116606365 4084070608021220293727387)
    ·
      refine ⟨6126105912031830440591081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4084070608021220293727387 6126105912031830440591081)
      ·
        refine ⟨4594579434023872830443311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6126105912031830440591081 4594579434023872830443311)
        ·
          refine ⟨6891869151035809245664967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594579434023872830443311 6891869151035809245664967)
          ·
            refine ⟨10337803726553713868497451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6891869151035809245664967 10337803726553713868497451)
            ·
              refine ⟨15506705589830570802746177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10337803726553713868497451 15506705589830570802746177)
              ·
                refine ⟨11630029192372928102059633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15506705589830570802746177 11630029192372928102059633)
                ·
                  refine ⟨8722521894279696076544725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11630029192372928102059633 8722521894279696076544725)
                  ·
                    refine ⟨204434106897180376794017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8722521894279696076544725 204434106897180376794017)
                    ·
                      rfl

theorem cell23_1194402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1194402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194402 prefixEnd_1194402 := by exact prefixLift 1194402
  have htrace : WordTrace (prefixWord ++ tailWord_1194402) baseStart_1194402 baseEnd_1194402 := by
    simpa [prefixWord, tailWord_1194402, baseEnd_1194402] using wordTrace_append hprefix tailTrace_1194402
  have hstable : (prefixWord ++ tailWord_1194402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194402).length < 2 ^ (prefixWord ++ tailWord_1194402).sum := by decide
  have hdescent : baseEnd_1194402 < baseStart_1194402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194420 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1194420 : Nat := 118140960795 + 1194420 * 2 ^ 59
def prefixEnd_1194420 : Nat := 4983230072969 + 3 ^ 40 * 1194420 * 2
def baseEnd_1194420 : Nat := 613311563343322059956969

theorem tailTrace_1194420 : CollatzResearch.WordTrace tailWord_1194420 prefixEnd_1194420 613311563343322059956969 := by
  unfold tailWord_1194420
  simp only [CollatzResearch.WordTrace]
  refine ⟨21782038166413902770290357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29042717555218537027053809 21782038166413902770290357)
  ·
    refine ⟨2042066078101303384714721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21782038166413902770290357 2042066078101303384714721)
    ·
      refine ⟨1531549558575977538536041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2042066078101303384714721 1531549558575977538536041)
      ·
        refine ⟨1148662168931983153902031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1531549558575977538536041 1148662168931983153902031)
        ·
          refine ⟨1722993253397974730853047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148662168931983153902031 1722993253397974730853047)
          ·
            refine ⟨2584489880096962096279571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722993253397974730853047 2584489880096962096279571)
            ·
              refine ⟨3876734820145443144419357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584489880096962096279571 3876734820145443144419357)
              ·
                refine ⟨1453775557554541179157259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3876734820145443144419357 1453775557554541179157259)
                ·
                  refine ⟨2180663336331811768735889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453775557554541179157259 2180663336331811768735889)
                  ·
                    refine ⟨1635497502248858826551917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2180663336331811768735889 1635497502248858826551917)
                    ·
                      refine ⟨613311563343322059956969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1635497502248858826551917 613311563343322059956969)
                      ·
                        rfl

theorem cell23_1194420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1194420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194420 prefixEnd_1194420 := by exact prefixLift 1194420
  have htrace : WordTrace (prefixWord ++ tailWord_1194420) baseStart_1194420 baseEnd_1194420 := by
    simpa [prefixWord, tailWord_1194420, baseEnd_1194420] using wordTrace_append hprefix tailTrace_1194420
  have hstable : (prefixWord ++ tailWord_1194420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194420).length < 2 ^ (prefixWord ++ tailWord_1194420).sum := by decide
  have hdescent : baseEnd_1194420 < baseStart_1194420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194450 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1194450 : Nat := 118140960795 + 1194450 * 2 ^ 59
def prefixEnd_1194450 : Nat := 4983230072969 + 3 ^ 40 * 1194450 * 2
def baseEnd_1194450 : Nat := 613326967762956942581831

theorem tailTrace_1194450 : CollatzResearch.WordTrace tailWord_1194450 prefixEnd_1194450 613326967762956942581831 := by
  unfold tailWord_1194450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891292630679780166043201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29043447015146080442781869 10891292630679780166043201)
  ·
    refine ⟨8168469473009835124532401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10891292630679780166043201 8168469473009835124532401)
    ·
      refine ⟨6126352104757376343399301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8168469473009835124532401 6126352104757376343399301)
      ·
        refine ⟨1148691019642008064387369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6126352104757376343399301 1148691019642008064387369)
        ·
          refine ⟨861518264731506048290527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148691019642008064387369 861518264731506048290527)
          ·
            refine ⟨1292277397097259072435791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861518264731506048290527 1292277397097259072435791)
            ·
              refine ⟨1938416095645888608653687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292277397097259072435791 1938416095645888608653687)
              ·
                refine ⟨2907624143468832912980531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938416095645888608653687 2907624143468832912980531)
                ·
                  refine ⟨4361436215203249369470797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907624143468832912980531 4361436215203249369470797)
                  ·
                    refine ⟨1635538580701218513551549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4361436215203249369470797 1635538580701218513551549)
                    ·
                      refine ⟨613326967762956942581831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1635538580701218513551549 613326967762956942581831)
                      ·
                        rfl

theorem cell23_1194450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1194450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194450 prefixEnd_1194450 := by exact prefixLift 1194450
  have htrace : WordTrace (prefixWord ++ tailWord_1194450) baseStart_1194450 baseEnd_1194450 := by
    simpa [prefixWord, tailWord_1194450, baseEnd_1194450] using wordTrace_append hprefix tailTrace_1194450
  have hstable : (prefixWord ++ tailWord_1194450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194450).length < 2 ^ (prefixWord ++ tailWord_1194450).sum := by decide
  have hdescent : baseEnd_1194450 < baseStart_1194450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194499 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 2, 5, 2]
def baseStart_1194499 : Nat := 118140960795 + 1194499 * 2 ^ 59
def prefixEnd_1194499 : Nat := 4983230072969 + 3 ^ 40 * 1194499 * 2
def baseEnd_1194499 : Nat := 613352128315027250869105

theorem tailTrace_1194499 : CollatzResearch.WordTrace tailWord_1194499 prefixEnd_1194499 613352128315027250869105 := by
  unfold tailWord_1194499
  simp only [CollatzResearch.WordTrace]
  refine ⟨43566957699541602032706551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29044638466361068021804367 43566957699541602032706551)
  ·
    refine ⟨65350436549312403049059827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43566957699541602032706551 65350436549312403049059827)
    ·
      refine ⟨98025654823968604573589741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65350436549312403049059827 98025654823968604573589741)
      ·
        refine ⟨36759620558988226715096153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98025654823968604573589741 36759620558988226715096153)
        ·
          refine ⟨27569715419241170036322115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36759620558988226715096153 27569715419241170036322115)
          ·
            refine ⟨41354573128861755054483173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27569715419241170036322115 41354573128861755054483173)
            ·
              refine ⟨7753982461661579072715595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41354573128861755054483173 7753982461661579072715595)
              ·
                refine ⟨11630973692492368609073393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7753982461661579072715595 11630973692492368609073393)
                ·
                  refine ⟨8723230269369276456805045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11630973692492368609073393 8723230269369276456805045)
                  ·
                    refine ⟨817802837753369667825473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8723230269369276456805045 817802837753369667825473)
                    ·
                      refine ⟨613352128315027250869105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817802837753369667825473 613352128315027250869105)
                      ·
                        rfl

theorem cell23_1194499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_1194499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194499 prefixEnd_1194499 := by exact prefixLift 1194499
  have htrace : WordTrace (prefixWord ++ tailWord_1194499) baseStart_1194499 baseEnd_1194499 := by
    simpa [prefixWord, tailWord_1194499, baseEnd_1194499] using wordTrace_append hprefix tailTrace_1194499
  have hstable : (prefixWord ++ tailWord_1194499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194499).length < 2 ^ (prefixWord ++ tailWord_1194499).sum := by decide
  have hdescent : baseEnd_1194499 < baseStart_1194499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194522 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_1194522 : Nat := 118140960795 + 1194522 * 2 ^ 59
def prefixEnd_1194522 : Nat := 4983230072969 + 3 ^ 40 * 1194522 * 2
def baseEnd_1194522 : Nat := 204454646123360220293833

theorem tailTrace_1194522 : CollatzResearch.WordTrace tailWord_1194522 prefixEnd_1194522 204454646123360220293833 := by
  unfold tailWord_1194522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891949144614569240198455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29045197718972184640529213 10891949144614569240198455)
  ·
    refine ⟨16337923716921853860297683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10891949144614569240198455 16337923716921853860297683)
    ·
      refine ⟨24506885575382780790446525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16337923716921853860297683 24506885575382780790446525)
      ·
        refine ⟨9190082090768542796417447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24506885575382780790446525 9190082090768542796417447)
        ·
          refine ⟨13785123136152814194626171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9190082090768542796417447 13785123136152814194626171)
          ·
            refine ⟨20677684704229221291939257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13785123136152814194626171 20677684704229221291939257)
            ·
              refine ⟨15508263528171915968954443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20677684704229221291939257 15508263528171915968954443)
              ·
                refine ⟨23262395292257873953431665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15508263528171915968954443 23262395292257873953431665)
                ·
                  refine ⟨17446796469193405465073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23262395292257873953431665 17446796469193405465073749)
                  ·
                    refine ⟨204454646123360220293833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17446796469193405465073749 204454646123360220293833)
                    ·
                      rfl

theorem cell23_1194522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_1194522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194522 prefixEnd_1194522 := by exact prefixLift 1194522
  have htrace : WordTrace (prefixWord ++ tailWord_1194522) baseStart_1194522 baseEnd_1194522 := by
    simpa [prefixWord, tailWord_1194522, baseEnd_1194522] using wordTrace_append hprefix tailTrace_1194522
  have hstable : (prefixWord ++ tailWord_1194522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194522).length < 2 ^ (prefixWord ++ tailWord_1194522).sum := by decide
  have hdescent : baseEnd_1194522 < baseStart_1194522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194573 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1194573 : Nat := 118140960795 + 1194573 * 2 ^ 59
def prefixEnd_1194573 : Nat := 4983230072969 + 3 ^ 40 * 1194573 * 2
def baseEnd_1194573 : Nat := 204463375294486653781255

theorem tailTrace_1194573 : CollatzResearch.WordTrace tailWord_1194573 prefixEnd_1194573 204463375294486653781255 := by
  unfold tailWord_1194573
  simp only [CollatzResearch.WordTrace]
  refine ⟨43569656701273512670900373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29046437800849008447266915 43569656701273512670900373)
  ·
    refine ⟨2042327657872195906448455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43569656701273512670900373 2042327657872195906448455)
    ·
      refine ⟨3063491486808293859672683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042327657872195906448455 3063491486808293859672683)
      ·
        refine ⟨4595237230212440789509025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063491486808293859672683 4595237230212440789509025)
        ·
          refine ⟨3446427922659330592131769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4595237230212440789509025 3446427922659330592131769)
          ·
            refine ⟨2584820941994497944098827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3446427922659330592131769 2584820941994497944098827)
            ·
              refine ⟨3877231412991746916148241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584820941994497944098827 3877231412991746916148241)
              ·
                refine ⟨2907923559743810187111181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877231412991746916148241 2907923559743810187111181)
                ·
                  refine ⟨1090471334903928820166693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2907923559743810187111181 1090471334903928820166693)
                  ·
                    refine ⟨204463375294486653781255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1090471334903928820166693 204463375294486653781255)
                    ·
                      rfl

theorem cell23_1194573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1194573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194573 prefixEnd_1194573 := by exact prefixLift 1194573
  have htrace : WordTrace (prefixWord ++ tailWord_1194573) baseStart_1194573 baseEnd_1194573 := by
    simpa [prefixWord, tailWord_1194573, baseEnd_1194573] using wordTrace_append hprefix tailTrace_1194573
  have hstable : (prefixWord ++ tailWord_1194573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194573).length < 2 ^ (prefixWord ++ tailWord_1194573).sum := by decide
  have hdescent : baseEnd_1194573 < baseStart_1194573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194596 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_1194596 : Nat := 118140960795 + 1194596 * 2 ^ 59
def prefixEnd_1194596 : Nat := 4983230072969 + 3 ^ 40 * 1194596 * 2
def baseEnd_1194596 : Nat := 613401935938513371356159

theorem tailTrace_1194596 : CollatzResearch.WordTrace tailWord_1194596 prefixEnd_1194596 613401935938513371356159 := by
  unfold tailWord_1194596
  simp only [CollatzResearch.WordTrace]
  refine ⟨21785247790095093799493821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29046997053460125065991761 21785247790095093799493821)
  ·
    refine ⟨8169467921285660174810183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21785247790095093799493821 8169467921285660174810183)
    ·
      refine ⟨12254201881928490262215275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8169467921285660174810183 12254201881928490262215275)
      ·
        refine ⟨18381302822892735393322913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12254201881928490262215275 18381302822892735393322913)
        ·
          refine ⟨13785977117169551544992185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18381302822892735393322913 13785977117169551544992185)
          ·
            refine ⟨10339482837877163658744139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13785977117169551544992185 10339482837877163658744139)
            ·
              refine ⟨15509224256815745488116209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339482837877163658744139 15509224256815745488116209)
              ·
                refine ⟨11631918192611809116087157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15509224256815745488116209 11631918192611809116087157)
                ·
                  refine ⟨1090492330557357104633171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11631918192611809116087157 1090492330557357104633171)
                  ·
                    refine ⟨1635738495836035656949757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1090492330557357104633171 1635738495836035656949757)
                    ·
                      refine ⟨613401935938513371356159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1635738495836035656949757 613401935938513371356159)
                      ·
                        rfl

theorem cell23_1194596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_1194596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194596 prefixEnd_1194596 := by exact prefixLift 1194596
  have htrace : WordTrace (prefixWord ++ tailWord_1194596) baseStart_1194596 baseEnd_1194596 := by
    simpa [prefixWord, tailWord_1194596, baseEnd_1194596] using wordTrace_append hprefix tailTrace_1194596
  have hstable : (prefixWord ++ tailWord_1194596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194596).length < 2 ^ (prefixWord ++ tailWord_1194596).sum := by decide
  have hdescent : baseEnd_1194596 < baseStart_1194596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194619 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4]
def baseStart_1194619 : Nat := 118140960795 + 1194619 * 2 ^ 59
def prefixEnd_1194619 : Nat := 4983230072969 + 3 ^ 40 * 1194619 * 2
def baseEnd_1194619 : Nat := 613413745993566781368553

theorem tailTrace_1194619 : CollatzResearch.WordTrace tailWord_1194619 prefixEnd_1194619 613413745993566781368553 := by
  unfold tailWord_1194619
  simp only [CollatzResearch.WordTrace]
  refine ⟨43571334459106862527074911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29047556306071241684716607 43571334459106862527074911)
  ·
    refine ⟨65357001688660293790612367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43571334459106862527074911 65357001688660293790612367)
    ·
      refine ⟨98035502532990440685918551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65357001688660293790612367 98035502532990440685918551)
      ·
        refine ⟨147053253799485661028877827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98035502532990440685918551 147053253799485661028877827)
        ·
          refine ⟨220579880699228491543316741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147053253799485661028877827 220579880699228491543316741)
          ·
            refine ⟨41358727631105342164371889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220579880699228491543316741 41358727631105342164371889)
            ·
              refine ⟨31019045723329006623278917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41358727631105342164371889 31019045723329006623278917)
              ·
                refine ⟨5816071073124188741864797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31019045723329006623278917 5816071073124188741864797)
                ·
                  refine ⟨2181026652421570778199299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5816071073124188741864797 2181026652421570778199299)
                  ·
                    refine ⟨3271539978632356167298949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2181026652421570778199299 3271539978632356167298949)
                    ·
                      refine ⟨613413745993566781368553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3271539978632356167298949 613413745993566781368553)
                      ·
                        rfl

theorem cell23_1194619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4].length) (baseStart_1194619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194619 prefixEnd_1194619 := by exact prefixLift 1194619
  have htrace : WordTrace (prefixWord ++ tailWord_1194619) baseStart_1194619 baseEnd_1194619 := by
    simpa [prefixWord, tailWord_1194619, baseEnd_1194619] using wordTrace_append hprefix tailTrace_1194619
  have hstable : (prefixWord ++ tailWord_1194619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194619).length < 2 ^ (prefixWord ++ tailWord_1194619).sum := by decide
  have hdescent : baseEnd_1194619 < baseStart_1194619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194649 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_1194649 : Nat := 118140960795 + 1194649 * 2 ^ 59
def prefixEnd_1194649 : Nat := 4983230072969 + 3 ^ 40 * 1194649 * 2
def baseEnd_1194649 : Nat := 613429150413201663993415

theorem tailTrace_1194649 : CollatzResearch.WordTrace tailWord_1194649 prefixEnd_1194649 613429150413201663993415 := by
  unfold tailWord_1194649
  simp only [CollatzResearch.WordTrace]
  refine ⟨43572428648998177650667001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29048285765998785100444667 43572428648998177650667001)
  ·
    refine ⟨32679321486748633238000251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43572428648998177650667001 32679321486748633238000251)
    ·
      refine ⟨49018982230122949857000377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32679321486748633238000251 49018982230122949857000377)
      ·
        refine ⟨36764236672592212392750283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49018982230122949857000377 36764236672592212392750283)
        ·
          refine ⟨55146355008888318589125425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36764236672592212392750283 55146355008888318589125425)
          ·
            refine ⟨41359766256666238941844069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55146355008888318589125425 41359766256666238941844069)
            ·
              refine ⟨7754956173124919801595763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41359766256666238941844069 7754956173124919801595763)
              ·
                refine ⟨11632434259687379702393645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7754956173124919801595763 11632434259687379702393645)
                ·
                  refine ⟨4362162847382767388397617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11632434259687379702393645 4362162847382767388397617)
                  ·
                    refine ⟨3271622135537075541298213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4362162847382767388397617 3271622135537075541298213)
                    ·
                      refine ⟨613429150413201663993415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3271622135537075541298213 613429150413201663993415)
                      ·
                        rfl

theorem cell23_1194649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_1194649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194649 prefixEnd_1194649 := by exact prefixLift 1194649
  have htrace : WordTrace (prefixWord ++ tailWord_1194649) baseStart_1194649 baseEnd_1194649 := by
    simpa [prefixWord, tailWord_1194649, baseEnd_1194649] using wordTrace_append hprefix tailTrace_1194649
  have hstable : (prefixWord ++ tailWord_1194649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194649).length < 2 ^ (prefixWord ++ tailWord_1194649).sum := by decide
  have hdescent : baseEnd_1194649 < baseStart_1194649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194653 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_1194653 : Nat := 118140960795 + 1194653 * 2 ^ 59
def prefixEnd_1194653 : Nat := 4983230072969 + 3 ^ 40 * 1194653 * 2
def baseEnd_1194653 : Nat := 613431204335819648343397

theorem tailTrace_1194653 : CollatzResearch.WordTrace tailWord_1194653 prefixEnd_1194653 613431204335819648343397 := by
  unfold tailWord_1194653
  simp only [CollatzResearch.WordTrace]
  refine ⟨43572574540983686333812613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29048383027322457555875075 43572574540983686333812613)
  ·
    refine ⟨8169857726434441187589865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43572574540983686333812613 8169857726434441187589865)
    ·
      refine ⟨6127393294825830890692399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8169857726434441187589865 6127393294825830890692399)
      ·
        refine ⟨9191089942238746336038599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127393294825830890692399 9191089942238746336038599)
        ·
          refine ⟨13786634913358119504057899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9191089942238746336038599 13786634913358119504057899)
          ·
            refine ⟨20679952370037179256086849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13786634913358119504057899 20679952370037179256086849)
            ·
              refine ⟨15509964277527884442065137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20679952370037179256086849 15509964277527884442065137)
              ·
                refine ⟨11632473208145913331548853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15509964277527884442065137 11632473208145913331548853)
                ·
                  refine ⟨1090544363263679374832705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11632473208145913331548853 1090544363263679374832705)
                  ·
                    refine ⟨817908272447759531124529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090544363263679374832705 817908272447759531124529)
                    ·
                      refine ⟨613431204335819648343397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817908272447759531124529 613431204335819648343397)
                      ·
                        rfl

theorem cell23_1194653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_1194653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194653 prefixEnd_1194653 := by exact prefixLift 1194653
  have htrace : WordTrace (prefixWord ++ tailWord_1194653) baseStart_1194653 baseEnd_1194653 := by
    simpa [prefixWord, tailWord_1194653, baseEnd_1194653] using wordTrace_append hprefix tailTrace_1194653
  have hstable : (prefixWord ++ tailWord_1194653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194653).length < 2 ^ (prefixWord ++ tailWord_1194653).sum := by decide
  have hdescent : baseEnd_1194653 < baseStart_1194653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194729 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_1194729 : Nat := 118140960795 + 1194729 * 2 ^ 59
def prefixEnd_1194729 : Nat := 4983230072969 + 3 ^ 40 * 1194729 * 2
def baseEnd_1194729 : Nat := 613470228865561350993047

theorem tailTrace_1194729 : CollatzResearch.WordTrace tailWord_1194729 prefixEnd_1194729 613470228865561350993047 := by
  unfold tailWord_1194729
  simp only [CollatzResearch.WordTrace]
  refine ⟨43575346488708351313579241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29050230992472234209052827 43575346488708351313579241)
  ·
    refine ⟨32681509866531263485184431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43575346488708351313579241 32681509866531263485184431)
    ·
      refine ⟨49022264799796895227776647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32681509866531263485184431 49022264799796895227776647)
      ·
        refine ⟨73533397199695342841664971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49022264799796895227776647 73533397199695342841664971)
        ·
          refine ⟨110300095799543014262497457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73533397199695342841664971 110300095799543014262497457)
          ·
            refine ⟨82725071849657260696873093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110300095799543014262497457 82725071849657260696873093)
            ·
              refine ⟨15510950971810736380663705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82725071849657260696873093 15510950971810736380663705)
              ·
                refine ⟨11633213228858052285497779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15510950971810736380663705 11633213228858052285497779)
                ·
                  refine ⟨17449819843287078428246669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11633213228858052285497779 17449819843287078428246669)
                  ·
                    refine ⟨6543682441232654410592501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17449819843287078428246669 6543682441232654410592501)
                    ·
                      refine ⟨613470228865561350993047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6543682441232654410592501 613470228865561350993047)
                      ·
                        rfl

theorem cell23_1194729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_1194729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194729 prefixEnd_1194729 := by exact prefixLift 1194729
  have htrace : WordTrace (prefixWord ++ tailWord_1194729) baseStart_1194729 baseEnd_1194729 := by
    simpa [prefixWord, tailWord_1194729, baseEnd_1194729] using wordTrace_append hprefix tailTrace_1194729
  have hstable : (prefixWord ++ tailWord_1194729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194729).length < 2 ^ (prefixWord ++ tailWord_1194729).sum := by decide
  have hdescent : baseEnd_1194729 < baseStart_1194729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194743 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_1194743 : Nat := 118140960795 + 1194743 * 2 ^ 59
def prefixEnd_1194743 : Nat := 4983230072969 + 3 ^ 40 * 1194743 * 2
def baseEnd_1194743 : Nat := 613477417594724296217983

theorem tailTrace_1194743 : CollatzResearch.WordTrace tailWord_1194743 prefixEnd_1194743 613477417594724296217983 := by
  unfold tailWord_1194743
  simp only [CollatzResearch.WordTrace]
  refine ⟨43575857110657631704588883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29050571407105087803059255 43575857110657631704588883)
  ·
    refine ⟨65363785665986447556883325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43575857110657631704588883 65363785665986447556883325)
    ·
      refine ⟨24511419624744917833831247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65363785665986447556883325 24511419624744917833831247)
      ·
        refine ⟨36767129437117376750746871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24511419624744917833831247 36767129437117376750746871)
        ·
          refine ⟨55150694155676065126120307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36767129437117376750746871 55150694155676065126120307)
          ·
            refine ⟨82726041233514097689180461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55150694155676065126120307 82726041233514097689180461)
            ·
              refine ⟨31022265462567786633442673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82726041233514097689180461 31022265462567786633442673)
              ·
                refine ⟨23266699096925839975082005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31022265462567786633442673 23266699096925839975082005)
                ·
                  refine ⟨1090626520168398748831969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23266699096925839975082005 1090626520168398748831969)
                  ·
                    refine ⟨817969890126299061623977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090626520168398748831969 817969890126299061623977)
                    ·
                      refine ⟨613477417594724296217983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 817969890126299061623977 613477417594724296217983)
                      ·
                        rfl

theorem cell23_1194743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_1194743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194743 prefixEnd_1194743 := by exact prefixLift 1194743
  have htrace : WordTrace (prefixWord ++ tailWord_1194743) baseStart_1194743 baseEnd_1194743 := by
    simpa [prefixWord, tailWord_1194743, baseEnd_1194743] using wordTrace_append hprefix tailTrace_1194743
  have hstable : (prefixWord ++ tailWord_1194743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194743).length < 2 ^ (prefixWord ++ tailWord_1194743).sum := by decide
  have hdescent : baseEnd_1194743 < baseStart_1194743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194756 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1194756 : Nat := 118140960795 + 1194756 * 2 ^ 59
def prefixEnd_1194756 : Nat := 4983230072969 + 3 ^ 40 * 1194756 * 2
def baseEnd_1194756 : Nat := 613484092843232745355423

theorem tailTrace_1194756 : CollatzResearch.WordTrace tailWord_1194756 prefixEnd_1194756 613484092843232745355423 := by
  unfold tailWord_1194756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21788165629805267462406061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29050887506407023283208081 21788165629805267462406061)
  ·
    refine ⟨8170562111176975298402273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21788165629805267462406061 8170562111176975298402273)
    ·
      refine ⟨6127921583382731473801705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8170562111176975298402273 6127921583382731473801705)
      ·
        refine ⟨4595941187537048605351279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6127921583382731473801705 4595941187537048605351279)
        ·
          refine ⟨6893911781305572908026919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595941187537048605351279 6893911781305572908026919)
          ·
            refine ⟨10340867671958359362040379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893911781305572908026919 10340867671958359362040379)
            ·
              refine ⟨15511301507937539043060569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10340867671958359362040379 15511301507937539043060569)
              ·
                refine ⟨11633476130953154282295427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15511301507937539043060569 11633476130953154282295427)
                ·
                  refine ⟨17450214196429731423443141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11633476130953154282295427 17450214196429731423443141)
                  ·
                    refine ⟨3271915161830574641895589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17450214196429731423443141 3271915161830574641895589)
                    ·
                      refine ⟨613484092843232745355423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3271915161830574641895589 613484092843232745355423)
                      ·
                        rfl

theorem cell23_1194756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1194756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194756 prefixEnd_1194756 := by exact prefixLift 1194756
  have htrace : WordTrace (prefixWord ++ tailWord_1194756) baseStart_1194756 baseEnd_1194756 := by
    simpa [prefixWord, tailWord_1194756, baseEnd_1194756] using wordTrace_append hprefix tailTrace_1194756
  have hstable : (prefixWord ++ tailWord_1194756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194756).length < 2 ^ (prefixWord ++ tailWord_1194756).sum := by decide
  have hdescent : baseEnd_1194756 < baseStart_1194756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194779 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 7]
def baseStart_1194779 : Nat := 118140960795 + 1194779 * 2 ^ 59
def prefixEnd_1194779 : Nat := 4983230072969 + 3 ^ 40 * 1194779 * 2
def baseEnd_1194779 : Nat := 204498634299428718455939

theorem tailTrace_1194779 : CollatzResearch.WordTrace tailWord_1194779 prefixEnd_1194779 204498634299428718455939 := by
  unfold tailWord_1194779
  simp only [CollatzResearch.WordTrace]
  refine ⟨43577170138527209852899391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29051446759018139901932927 43577170138527209852899391)
  ·
    refine ⟨65365755207790814779349087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43577170138527209852899391 65365755207790814779349087)
    ·
      refine ⟨98048632811686222169023631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65365755207790814779349087 98048632811686222169023631)
      ·
        refine ⟨147072949217529333253535447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98048632811686222169023631 147072949217529333253535447)
        ·
          refine ⟨220609423826293999880303171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147072949217529333253535447 220609423826293999880303171)
          ·
            refine ⟨330914135739440999820454757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220609423826293999880303171 330914135739440999820454757)
            ·
              refine ⟨62046400451145187466335267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 330914135739440999820454757 62046400451145187466335267)
              ·
                refine ⟨93069600676717781199502901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62046400451145187466335267 93069600676717781199502901)
                ·
                  refine ⟨8725275063442291987453397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93069600676717781199502901 8725275063442291987453397)
                  ·
                    refine ⟨204498634299428718455939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8725275063442291987453397 204498634299428718455939)
                    ·
                      rfl

theorem cell23_1194779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_1194779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194779 prefixEnd_1194779 := by exact prefixLift 1194779
  have htrace : WordTrace (prefixWord ++ tailWord_1194779) baseStart_1194779 baseEnd_1194779 := by
    simpa [prefixWord, tailWord_1194779, baseEnd_1194779] using wordTrace_append hprefix tailTrace_1194779
  have hstable : (prefixWord ++ tailWord_1194779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194779).length < 2 ^ (prefixWord ++ tailWord_1194779).sum := by decide
  have hdescent : baseEnd_1194779 < baseStart_1194779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194783 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 5]
def baseStart_1194783 : Nat := 118140960795 + 1194783 * 2 ^ 59
def prefixEnd_1194783 : Nat := 4983230072969 + 3 ^ 40 * 1194783 * 2
def baseEnd_1194783 : Nat := 68166439646767126635311

theorem tailTrace_1194783 : CollatzResearch.WordTrace tailWord_1194783 prefixEnd_1194783 68166439646767126635311 := by
  unfold tailWord_1194783
  simp only [CollatzResearch.WordTrace]
  refine ⟨43577316030512718536045003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29051544020341812357363335 43577316030512718536045003)
  ·
    refine ⟨65365974045769077804067505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43577316030512718536045003 65365974045769077804067505)
    ·
      refine ⟨49024480534326808353050629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65365974045769077804067505 49024480534326808353050629)
      ·
        refine ⟨9192090100186276566196993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49024480534326808353050629 9192090100186276566196993)
        ·
          refine ⟨6894067575139707424647745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9192090100186276566196993 6894067575139707424647745)
          ·
            refine ⟨5170550681354780568485809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6894067575139707424647745 5170550681354780568485809)
            ·
              refine ⟨3877913011016085426364357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5170550681354780568485809 3877913011016085426364357)
              ·
                refine ⟨727108689565516017443317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3877913011016085426364357 727108689565516017443317)
                ·
                  refine ⟨68166439646767126635311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 727108689565516017443317 68166439646767126635311)
                  ·
                    rfl

theorem cell23_1194783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 5].length) (baseStart_1194783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194783 prefixEnd_1194783 := by exact prefixLift 1194783
  have htrace : WordTrace (prefixWord ++ tailWord_1194783) baseStart_1194783 baseEnd_1194783 := by
    simpa [prefixWord, tailWord_1194783, baseEnd_1194783] using wordTrace_append hprefix tailTrace_1194783
  have hstable : (prefixWord ++ tailWord_1194783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194783).length < 2 ^ (prefixWord ++ tailWord_1194783).sum := by decide
  have hdescent : baseEnd_1194783 < baseStart_1194783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194794 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1194794 : Nat := 118140960795 + 1194794 * 2 ^ 59
def prefixEnd_1194794 : Nat := 4983230072969 + 3 ^ 40 * 1194794 * 2
def baseEnd_1194794 : Nat := 613503605108103596680249

theorem tailTrace_1194794 : CollatzResearch.WordTrace tailWord_1194794 prefixEnd_1194794 613503605108103596680249 := by
  unfold tailWord_1194794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10894429308368216853673859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29051811488981911609796957 10894429308368216853673859)
  ·
    refine ⟨16341643962552325280510789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10894429308368216853673859 16341643962552325280510789)
    ·
      refine ⟨3064058242978560990095773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16341643962552325280510789 3064058242978560990095773)
      ·
        refine ⟨1149021841116960371285915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3064058242978560990095773 1149021841116960371285915)
        ·
          refine ⟨1723532761675440556928873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149021841116960371285915 1723532761675440556928873)
          ·
            refine ⟨1292649571256580417696655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1723532761675440556928873 1292649571256580417696655)
            ·
              refine ⟨1938974356884870626544983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292649571256580417696655 1938974356884870626544983)
              ·
                refine ⟨2908461535327305939817475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938974356884870626544983 2908461535327305939817475)
                ·
                  refine ⟨4362692302990958909726213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908461535327305939817475 4362692302990958909726213)
                  ·
                    refine ⟨818004806810804795573665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362692302990958909726213 818004806810804795573665)
                    ·
                      refine ⟨613503605108103596680249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818004806810804795573665 613503605108103596680249)
                      ·
                        rfl

theorem cell23_1194794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1194794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194794 prefixEnd_1194794 := by exact prefixLift 1194794
  have htrace : WordTrace (prefixWord ++ tailWord_1194794) baseStart_1194794 baseEnd_1194794 := by
    simpa [prefixWord, tailWord_1194794, baseEnd_1194794] using wordTrace_append hprefix tailTrace_1194794
  have hstable : (prefixWord ++ tailWord_1194794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194794).length < 2 ^ (prefixWord ++ tailWord_1194794).sum := by decide
  have hdescent : baseEnd_1194794 < baseStart_1194794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194816 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_1194816 : Nat := 118140960795 + 1194816 * 2 ^ 59
def prefixEnd_1194816 : Nat := 4983230072969 + 3 ^ 40 * 1194816 * 2
def baseEnd_1194816 : Nat := 613514901682502510605147

theorem tailTrace_1194816 : CollatzResearch.WordTrace tailWord_1194816 prefixEnd_1194816 613514901682502510605147 := by
  unfold tailWord_1194816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789259819696582585998151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29052346426262110114664201 21789259819696582585998151)
  ·
    refine ⟨32683889729544873878997227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21789259819696582585998151 32683889729544873878997227)
    ·
      refine ⟨49025834594317310818495841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32683889729544873878997227 49025834594317310818495841)
      ·
        refine ⟨36769375945737983113871881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49025834594317310818495841 36769375945737983113871881)
        ·
          refine ⟨27577031959303487335403911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36769375945737983113871881 27577031959303487335403911)
          ·
            refine ⟨41365547938955231003105867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27577031959303487335403911 41365547938955231003105867)
            ·
              refine ⟨62048321908432846504658801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41365547938955231003105867 62048321908432846504658801)
              ·
                refine ⟨46536241431324634878494101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62048321908432846504658801 46536241431324634878494101)
                ·
                  refine ⟨2181386317093342259929411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46536241431324634878494101 2181386317093342259929411)
                  ·
                    refine ⟨3272079475640013389894117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2181386317093342259929411 3272079475640013389894117)
                    ·
                      refine ⟨613514901682502510605147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3272079475640013389894117 613514901682502510605147)
                      ·
                        rfl

theorem cell23_1194816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_1194816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194816 prefixEnd_1194816 := by exact prefixLift 1194816
  have htrace : WordTrace (prefixWord ++ tailWord_1194816) baseStart_1194816 baseEnd_1194816 := by
    simpa [prefixWord, tailWord_1194816, baseEnd_1194816] using wordTrace_append hprefix tailTrace_1194816
  have hstable : (prefixWord ++ tailWord_1194816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194816).length < 2 ^ (prefixWord ++ tailWord_1194816).sum := by decide
  have hdescent : baseEnd_1194816 < baseStart_1194816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194890 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_1194890 : Nat := 118140960795 + 1194890 * 2 ^ 59
def prefixEnd_1194890 : Nat := 4983230072969 + 3 ^ 40 * 1194890 * 2
def baseEnd_1194890 : Nat := 68172544361215024564423

theorem tailTrace_1194890 : CollatzResearch.WordTrace tailWord_1194890 prefixEnd_1194890 68172544361215024564423 := by
  unfold tailWord_1194890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895304660281268952547531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29054145760750050540126749 10895304660281268952547531)
  ·
    refine ⟨16342956990421903428821297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895304660281268952547531 16342956990421903428821297)
    ·
      refine ⟨12257217742816427571615973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16342956990421903428821297 12257217742816427571615973)
      ·
        refine ⟨2298228326778080169677995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12257217742816427571615973 2298228326778080169677995)
        ·
          refine ⟨3447342490167120254516993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298228326778080169677995 3447342490167120254516993)
          ·
            refine ⟨2585506867625340190887745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3447342490167120254516993 2585506867625340190887745)
            ·
              refine ⟨1939130150719005143165809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2585506867625340190887745 1939130150719005143165809)
              ·
                refine ⟨1454347613039253857374357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1939130150719005143165809 1454347613039253857374357)
                ·
                  refine ⟨68172544361215024564423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1454347613039253857374357 68172544361215024564423)
                  ·
                    rfl

theorem cell23_1194890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_1194890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194890 prefixEnd_1194890 := by exact prefixLift 1194890
  have htrace : WordTrace (prefixWord ++ tailWord_1194890) baseStart_1194890 baseEnd_1194890 := by
    simpa [prefixWord, tailWord_1194890, baseEnd_1194890] using wordTrace_append hprefix tailTrace_1194890
  have hstable : (prefixWord ++ tailWord_1194890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194890).length < 2 ^ (prefixWord ++ tailWord_1194890).sum := by decide
  have hdescent : baseEnd_1194890 < baseStart_1194890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194923 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 2, 6, 2]
def baseStart_1194923 : Nat := 118140960795 + 1194923 * 2 ^ 59
def prefixEnd_1194923 : Nat := 4983230072969 + 3 ^ 40 * 1194923 * 2
def baseEnd_1194923 : Nat := 613569844112533591967155

theorem tailTrace_1194923 : CollatzResearch.WordTrace tailWord_1194923 prefixEnd_1194923 613569844112533591967155 := by
  unfold tailWord_1194923
  simp only [CollatzResearch.WordTrace]
  refine ⟨43582422250005522446141423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29054948166670348297427615 43582422250005522446141423)
  ·
    refine ⟨65373633375008283669212135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43582422250005522446141423 65373633375008283669212135)
    ·
      refine ⟨98060450062512425503818203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65373633375008283669212135 98060450062512425503818203)
      ·
        refine ⟨147090675093768638255727305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98060450062512425503818203 147090675093768638255727305)
        ·
          refine ⟨110318006320326478691795479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147090675093768638255727305 110318006320326478691795479)
          ·
            refine ⟨165477009480489718037693219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110318006320326478691795479 165477009480489718037693219)
            ·
              refine ⟨248215514220734577056539829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165477009480489718037693219 248215514220734577056539829)
              ·
                refine ⟨23270204458193866599050609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248215514220734577056539829 23270204458193866599050609)
                ·
                  refine ⟨17452653343645399949287957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23270204458193866599050609 17452653343645399949287957)
                  ·
                    refine ⟨818093125483378122622873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17452653343645399949287957 818093125483378122622873)
                    ·
                      refine ⟨613569844112533591967155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818093125483378122622873 613569844112533591967155)
                      ·
                        rfl

theorem cell23_1194923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 6, 2].length) (baseStart_1194923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194923 prefixEnd_1194923 := by exact prefixLift 1194923
  have htrace : WordTrace (prefixWord ++ tailWord_1194923) baseStart_1194923 baseEnd_1194923 := by
    simpa [prefixWord, tailWord_1194923, baseEnd_1194923] using wordTrace_append hprefix tailTrace_1194923
  have hstable : (prefixWord ++ tailWord_1194923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194923).length < 2 ^ (prefixWord ++ tailWord_1194923).sum := by decide
  have hdescent : baseEnd_1194923 < baseStart_1194923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194933 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1194933 : Nat := 118140960795 + 1194933 * 2 ^ 59
def prefixEnd_1194933 : Nat := 4983230072969 + 3 ^ 40 * 1194933 * 2
def baseEnd_1194933 : Nat := 204524992973026184280703

theorem tailTrace_1194933 : CollatzResearch.WordTrace tailWord_1194933 prefixEnd_1194933 204524992973026184280703 := by
  unfold tailWord_1194933
  simp only [CollatzResearch.WordTrace]
  refine ⟨43582786979969294154005453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29055191319979529436003635 43582786979969294154005453)
  ·
    refine ⟨16343545117488485307752045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43582786979969294154005453 16343545117488485307752045)
    ·
      refine ⟨6128829419058181990407017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16343545117488485307752045 6128829419058181990407017)
      ·
        refine ⟨4596622064293636492805263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6128829419058181990407017 4596622064293636492805263)
        ·
          refine ⟨6894933096440454739207895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596622064293636492805263 6894933096440454739207895)
          ·
            refine ⟨10342399644660682108811843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6894933096440454739207895 10342399644660682108811843)
            ·
              refine ⟨15513599466991023163217765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10342399644660682108811843 15513599466991023163217765)
              ·
                refine ⟨2908799900060816843103331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15513599466991023163217765 2908799900060816843103331)
                ·
                  refine ⟨4363199850091225264654997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908799900060816843103331 4363199850091225264654997)
                  ·
                    refine ⟨204524992973026184280703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4363199850091225264654997 204524992973026184280703)
                    ·
                      rfl

theorem cell23_1194933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1194933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194933 prefixEnd_1194933 := by exact prefixLift 1194933
  have htrace : WordTrace (prefixWord ++ tailWord_1194933) baseStart_1194933 baseEnd_1194933 := by
    simpa [prefixWord, tailWord_1194933, baseEnd_1194933] using wordTrace_append hprefix tailTrace_1194933
  have hstable : (prefixWord ++ tailWord_1194933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194933).length < 2 ^ (prefixWord ++ tailWord_1194933).sum := by decide
  have hdescent : baseEnd_1194933 < baseStart_1194933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194937 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 1, 5]
def baseStart_1194937 : Nat := 118140960795 + 1194937 * 2 ^ 59
def prefixEnd_1194937 : Nat := 4983230072969 + 3 ^ 40 * 1194937 * 2
def baseEnd_1194937 : Nat := 204525677613898845730697

theorem tailTrace_1194937 : CollatzResearch.WordTrace tailWord_1194937 prefixEnd_1194937 204525677613898845730697 := by
  unfold tailWord_1194937
  simp only [CollatzResearch.WordTrace]
  refine ⟨43582932871954802837151065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29055288581303201891434043 43582932871954802837151065)
  ·
    refine ⟨32687199653966102127863299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43582932871954802837151065 32687199653966102127863299)
    ·
      refine ⟨49030799480949153191794949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32687199653966102127863299 49030799480949153191794949)
      ·
        refine ⟨9193274902677966223461553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49030799480949153191794949 9193274902677966223461553)
        ·
          refine ⟨6894956177008474667596165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9193274902677966223461553 6894956177008474667596165)
          ·
            refine ⟨1292804283189089000174281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6894956177008474667596165 1292804283189089000174281)
            ·
              refine ⟨969603212391816750130711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292804283189089000174281 969603212391816750130711)
              ·
                refine ⟨1454404818587725125196067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969603212391816750130711 1454404818587725125196067)
                ·
                  refine ⟨2181607227881587687794101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454404818587725125196067 2181607227881587687794101)
                  ·
                    refine ⟨204525677613898845730697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2181607227881587687794101 204525677613898845730697)
                    ·
                      rfl

theorem cell23_1194937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_1194937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194937 prefixEnd_1194937 := by exact prefixLift 1194937
  have htrace : WordTrace (prefixWord ++ tailWord_1194937) baseStart_1194937 baseEnd_1194937 := by
    simpa [prefixWord, tailWord_1194937, baseEnd_1194937] using wordTrace_append hprefix tailTrace_1194937
  have hstable : (prefixWord ++ tailWord_1194937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194937).length < 2 ^ (prefixWord ++ tailWord_1194937).sum := by decide
  have hdescent : baseEnd_1194937 < baseStart_1194937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194943 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_1194943 : Nat := 118140960795 + 1194943 * 2 ^ 59
def prefixEnd_1194943 : Nat := 4983230072969 + 3 ^ 40 * 1194943 * 2
def baseEnd_1194943 : Nat := 613580113725623513717063

theorem tailTrace_1194943 : CollatzResearch.WordTrace tailWord_1194943 prefixEnd_1194943 613580113725623513717063 := by
  unfold tailWord_1194943
  simp only [CollatzResearch.WordTrace]
  refine ⟨43583151709933065861869483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29055434473288710574579655 43583151709933065861869483)
  ·
    refine ⟨65374727564899598792804225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43583151709933065861869483 65374727564899598792804225)
    ·
      refine ⟨49031045673674699094603169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65374727564899598792804225 49031045673674699094603169)
      ·
        refine ⟨36773284255256024320952377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49031045673674699094603169 36773284255256024320952377)
        ·
          refine ⟨27579963191442018240714283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36773284255256024320952377 27579963191442018240714283)
          ·
            refine ⟨41369944787163027361071425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27579963191442018240714283 41369944787163027361071425)
            ·
              refine ⟨31027458590372270520803569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41369944787163027361071425 31027458590372270520803569)
              ·
                refine ⟨23270593942779202890602677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31027458590372270520803569 23270593942779202890602677)
                ·
                  refine ⟨2181618182135550270994001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23270593942779202890602677 2181618182135550270994001)
                  ·
                    refine ⟨1636213636601662703245501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2181618182135550270994001 1636213636601662703245501)
                    ·
                      refine ⟨613580113725623513717063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1636213636601662703245501 613580113725623513717063)
                      ·
                        rfl

theorem cell23_1194943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_1194943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194943 prefixEnd_1194943 := by exact prefixLift 1194943
  have htrace : WordTrace (prefixWord ++ tailWord_1194943) baseStart_1194943 baseEnd_1194943 := by
    simpa [prefixWord, tailWord_1194943, baseEnd_1194943] using wordTrace_append hprefix tailTrace_1194943
  have hstable : (prefixWord ++ tailWord_1194943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194943).length < 2 ^ (prefixWord ++ tailWord_1194943).sum := by decide
  have hdescent : baseEnd_1194943 < baseStart_1194943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194970 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1194970 : Nat := 118140960795 + 1194970 * 2 ^ 59
def prefixEnd_1194970 : Nat := 4983230072969 + 3 ^ 40 * 1194970 * 2
def baseEnd_1194970 : Nat := 613593977703294908079439

theorem tailTrace_1194970 : CollatzResearch.WordTrace tailWord_1194970 prefixEnd_1194970 613593977703294908079439 := by
  unfold tailWord_1194970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10896034120208812368275591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29056090987223499648734909 10896034120208812368275591)
  ·
    refine ⟨16344051180313218552413387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10896034120208812368275591 16344051180313218552413387)
    ·
      refine ⟨24516076770469827828620081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16344051180313218552413387 24516076770469827828620081)
      ·
        refine ⟨18387057577852370871465061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24516076770469827828620081 18387057577852370871465061)
        ·
          refine ⟨3447573295847319538399699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18387057577852370871465061 3447573295847319538399699)
          ·
            refine ⟨5171359943770979307599549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447573295847319538399699 5171359943770979307599549)
            ·
              refine ⟨1939259978914117240349831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5171359943770979307599549 1939259978914117240349831)
              ·
                refine ⟨2908889968371175860524747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939259978914117240349831 2908889968371175860524747)
                ·
                  refine ⟨4363334952556763790787121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908889968371175860524747 4363334952556763790787121)
                  ·
                    refine ⟨3272501214417572843090341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4363334952556763790787121 3272501214417572843090341)
                    ·
                      refine ⟨613593977703294908079439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3272501214417572843090341 613593977703294908079439)
                      ·
                        rfl

theorem cell23_1194970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1194970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194970 prefixEnd_1194970 := by exact prefixLift 1194970
  have htrace : WordTrace (prefixWord ++ tailWord_1194970) baseStart_1194970 baseEnd_1194970 := by
    simpa [prefixWord, tailWord_1194970, baseEnd_1194970] using wordTrace_append hprefix tailTrace_1194970
  have hstable : (prefixWord ++ tailWord_1194970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194970).length < 2 ^ (prefixWord ++ tailWord_1194970).sum := by decide
  have hdescent : baseEnd_1194970 < baseStart_1194970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194991 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 1, 2, 2]
def baseStart_1194991 : Nat := 118140960795 + 1194991 * 2 ^ 59
def prefixEnd_1194991 : Nat := 4983230072969 + 3 ^ 40 * 1194991 * 2
def baseEnd_1194991 : Nat := 613604760797039325916843

theorem tailTrace_1194991 : CollatzResearch.WordTrace tailWord_1194991 prefixEnd_1194991 613604760797039325916843 := by
  unfold tailWord_1194991
  simp only [CollatzResearch.WordTrace]
  refine ⟨43584902413759170059616827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29056601609172780039744551 43584902413759170059616827)
  ·
    refine ⟨65377353620638755089425241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43584902413759170059616827 65377353620638755089425241)
    ·
      refine ⟨49033015215479066317068931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65377353620638755089425241 49033015215479066317068931)
      ·
        refine ⟨73549522823218599475603397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49033015215479066317068931 73549522823218599475603397)
        ·
          refine ⟨13790535529353487401675637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73549522823218599475603397 13790535529353487401675637)
          ·
            refine ⟨1292862705876889443907091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13790535529353487401675637 1292862705876889443907091)
            ·
              refine ⟨1939294058815334165860637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292862705876889443907091 1939294058815334165860637)
              ·
                refine ⟨727235272055750312197739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1939294058815334165860637 727235272055750312197739)
                ·
                  refine ⟨1090852908083625468296609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727235272055750312197739 1090852908083625468296609)
                  ·
                    refine ⟨818139681062719101222457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090852908083625468296609 818139681062719101222457)
                    ·
                      refine ⟨613604760797039325916843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818139681062719101222457 613604760797039325916843)
                      ·
                        rfl

theorem cell23_1194991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 2, 2].length) (baseStart_1194991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194991 prefixEnd_1194991 := by exact prefixLift 1194991
  have htrace : WordTrace (prefixWord ++ tailWord_1194991) baseStart_1194991 baseEnd_1194991 := by
    simpa [prefixWord, tailWord_1194991, baseEnd_1194991] using wordTrace_append hprefix tailTrace_1194991
  have hstable : (prefixWord ++ tailWord_1194991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194991).length < 2 ^ (prefixWord ++ tailWord_1194991).sum := by decide
  have hdescent : baseEnd_1194991 < baseStart_1194991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194997 : List Nat := [1, 3, 5, 2, 1, 2, 9]
def baseStart_1194997 : Nat := 118140960795 + 1194997 * 2 ^ 59
def prefixEnd_1194997 : Nat := 4983230072969 + 3 ^ 40 * 1194997 * 2
def baseEnd_1194997 : Nat := 7575405452851435832615

theorem tailTrace_1194997 : CollatzResearch.WordTrace tailWord_1194997 prefixEnd_1194997 7575405452851435832615 := by
  unfold tailWord_1194997
  simp only [CollatzResearch.WordTrace]
  refine ⟨43585121251737433084335245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29056747501158288722890163 43585121251737433084335245)
  ·
    refine ⟨16344420469401537406625717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43585121251737433084335245 16344420469401537406625717)
    ·
      refine ⟨1532289419006394131871161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16344420469401537406625717 1532289419006394131871161)
      ·
        refine ⟨1149217064254795598903371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532289419006394131871161 1149217064254795598903371)
        ·
          refine ⟨1723825596382193398355057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149217064254795598903371 1723825596382193398355057)
          ·
            refine ⟨1292869197286645048766293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1723825596382193398355057 1292869197286645048766293)
            ·
              refine ⟨7575405452851435832615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1292869197286645048766293 7575405452851435832615)
              ·
                rfl

theorem cell23_1194997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 9].length) (baseStart_1194997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1194997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1194997 prefixEnd_1194997 := by exact prefixLift 1194997
  have htrace : WordTrace (prefixWord ++ tailWord_1194997) baseStart_1194997 baseEnd_1194997 := by
    simpa [prefixWord, tailWord_1194997, baseEnd_1194997] using wordTrace_append hprefix tailTrace_1194997
  have hstable : (prefixWord ++ tailWord_1194997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194997).length < 2 ^ (prefixWord ++ tailWord_1194997).sum := by decide
  have hdescent : baseEnd_1194997 < baseStart_1194997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195000 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_1195000 : Nat := 118140960795 + 1195000 * 2 ^ 59
def prefixEnd_1195000 : Nat := 4983230072969 + 3 ^ 40 * 1195000 * 2
def baseEnd_1195000 : Nat := 613609382122929790704301

theorem tailTrace_1195000 : CollatzResearch.WordTrace tailWord_1195000 prefixEnd_1195000 613609382122929790704301 := by
  unfold tailWord_1195000
  simp only [CollatzResearch.WordTrace]
  refine ⟨21792615335363282298347227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29056820447151043064462969 21792615335363282298347227)
  ·
    refine ⟨32688923003044923447520841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21792615335363282298347227 32688923003044923447520841)
    ·
      refine ⟨24516692252283692585640631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32688923003044923447520841 24516692252283692585640631)
      ·
        refine ⟨36775038378425538878460947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24516692252283692585640631 36775038378425538878460947)
        ·
          refine ⟨55162557567638308317691421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36775038378425538878460947 55162557567638308317691421)
          ·
            refine ⟨20685959087864365619134283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55162557567638308317691421 20685959087864365619134283)
            ·
              refine ⟨31028938631796548428701425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20685959087864365619134283 31028938631796548428701425)
              ·
                refine ⟨23271703973847411321526069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31028938631796548428701425 23271703973847411321526069)
                ·
                  refine ⟨2181722247548194811393069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23271703973847411321526069 2181722247548194811393069)
                  ·
                    refine ⟨818145842830573054272401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181722247548194811393069 818145842830573054272401)
                    ·
                      refine ⟨613609382122929790704301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818145842830573054272401 613609382122929790704301)
                      ·
                        rfl

theorem cell23_1195000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_1195000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195000 prefixEnd_1195000 := by exact prefixLift 1195000
  have htrace : WordTrace (prefixWord ++ tailWord_1195000) baseStart_1195000 baseEnd_1195000 := by
    simpa [prefixWord, tailWord_1195000, baseEnd_1195000] using wordTrace_append hprefix tailTrace_1195000
  have hstable : (prefixWord ++ tailWord_1195000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195000).length < 2 ^ (prefixWord ++ tailWord_1195000).sum := by decide
  have hdescent : baseEnd_1195000 < baseStart_1195000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195013 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_1195013 : Nat := 118140960795 + 1195013 * 2 ^ 59
def prefixEnd_1195013 : Nat := 4983230072969 + 3 ^ 40 * 1195013 * 2
def baseEnd_1195013 : Nat := 613616057371438239841741

theorem tailTrace_1195013 : CollatzResearch.WordTrace tailWord_1195013 prefixEnd_1195013 613616057371438239841741 := by
  unfold tailWord_1195013
  simp only [CollatzResearch.WordTrace]
  refine ⟨43585704819679467816917693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29057136546452978544611795 43585704819679467816917693)
  ·
    refine ⟨16344639307379800431344135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43585704819679467816917693 16344639307379800431344135)
    ·
      refine ⟨24516958961069700647016203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16344639307379800431344135 24516958961069700647016203)
      ·
        refine ⟨36775438441604550970524305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24516958961069700647016203 36775438441604550970524305)
        ·
          refine ⟨27581578831203413227893229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36775438441604550970524305 27581578831203413227893229)
          ·
            refine ⟨10343092061701279960459961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27581578831203413227893229 10343092061701279960459961)
            ·
              refine ⟨7757319046275959970344971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10343092061701279960459961 7757319046275959970344971)
              ·
                refine ⟨11635978569413939955517457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7757319046275959970344971 11635978569413939955517457)
                ·
                  refine ⟨8726983927060454966638093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11635978569413939955517457 8726983927060454966638093)
                  ·
                    refine ⟨3272618972647670612489285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8726983927060454966638093 3272618972647670612489285)
                    ·
                      refine ⟨613616057371438239841741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3272618972647670612489285 613616057371438239841741)
                      ·
                        rfl

theorem cell23_1195013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_1195013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195013 prefixEnd_1195013 := by exact prefixLift 1195013
  have htrace : WordTrace (prefixWord ++ tailWord_1195013) baseStart_1195013 baseEnd_1195013 := by
    simpa [prefixWord, tailWord_1195013, baseEnd_1195013] using wordTrace_append hprefix tailTrace_1195013
  have hstable : (prefixWord ++ tailWord_1195013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195013).length < 2 ^ (prefixWord ++ tailWord_1195013).sum := by decide
  have hdescent : baseEnd_1195013 < baseStart_1195013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195033 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_1195033 : Nat := 118140960795 + 1195033 * 2 ^ 59
def prefixEnd_1195033 : Nat := 4983230072969 + 3 ^ 40 * 1195033 * 2
def baseEnd_1195033 : Nat := 613626326984528161591649

theorem tailTrace_1195033 : CollatzResearch.WordTrace tailWord_1195033 prefixEnd_1195033 613626326984528161591649 := by
  unfold tailWord_1195033
  simp only [CollatzResearch.WordTrace]
  refine ⟨43586434279607011232645753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29057622853071340821763835 43586434279607011232645753)
  ·
    refine ⟨32689825709705258424484315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43586434279607011232645753 32689825709705258424484315)
    ·
      refine ⟨49034738564557887636726473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32689825709705258424484315 49034738564557887636726473)
      ·
        refine ⟨36776053923418415727544855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49034738564557887636726473 36776053923418415727544855)
        ·
          refine ⟨55164080885127623591317283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36776053923418415727544855 55164080885127623591317283)
          ·
            refine ⟨82746121327691435386975925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55164080885127623591317283 82746121327691435386975925)
            ·
              refine ⟨7757448874471072067528993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82746121327691435386975925 7757448874471072067528993)
              ·
                refine ⟨5818086655853304050646745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7757448874471072067528993 5818086655853304050646745)
                ·
                  refine ⟨4363564991889978037985059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818086655853304050646745 4363564991889978037985059)
                  ·
                    refine ⟨6545347487834967056977589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4363564991889978037985059 6545347487834967056977589)
                    ·
                      refine ⟨613626326984528161591649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6545347487834967056977589 613626326984528161591649)
                      ·
                        rfl

theorem cell23_1195033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_1195033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195033 prefixEnd_1195033 := by exact prefixLift 1195033
  have htrace : WordTrace (prefixWord ++ tailWord_1195033) baseStart_1195033 baseEnd_1195033 := by
    simpa [prefixWord, tailWord_1195033, baseEnd_1195033] using wordTrace_append hprefix tailTrace_1195033
  have hstable : (prefixWord ++ tailWord_1195033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195033).length < 2 ^ (prefixWord ++ tailWord_1195033).sum := by decide
  have hdescent : baseEnd_1195033 < baseStart_1195033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195064 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_1195064 : Nat := 118140960795 + 1195064 * 2 ^ 59
def prefixEnd_1195064 : Nat := 4983230072969 + 3 ^ 40 * 1195064 * 2
def baseEnd_1195064 : Nat := 613642244884817540304007

theorem tailTrace_1195064 : CollatzResearch.WordTrace tailWord_1195064 prefixEnd_1195064 613642244884817540304007 := by
  unfold tailWord_1195064
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793782471247351763512123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29058376628329802351349497 21793782471247351763512123)
  ·
    refine ⟨32690673706871027645268185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21793782471247351763512123 32690673706871027645268185)
    ·
      refine ⟨24518005280153270733951139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32690673706871027645268185 24518005280153270733951139)
      ·
        refine ⟨36777007920229906100926709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24518005280153270733951139 36777007920229906100926709)
        ·
          refine ⟨3447844492521553696961879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36777007920229906100926709 3447844492521553696961879)
          ·
            refine ⟨5171766738782330545442819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447844492521553696961879 5171766738782330545442819)
            ·
              refine ⟨7757650108173495818164229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5171766738782330545442819 7757650108173495818164229)
              ·
                refine ⟨1454559395282530465905793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7757650108173495818164229 1454559395282530465905793)
                ·
                  refine ⟨1090919546461897849429345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1454559395282530465905793 1090919546461897849429345)
                  ·
                    refine ⟨818189659846423387072009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090919546461897849429345 818189659846423387072009)
                    ·
                      refine ⟨613642244884817540304007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818189659846423387072009 613642244884817540304007)
                      ·
                        rfl

theorem cell23_1195064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_1195064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195064 prefixEnd_1195064 := by exact prefixLift 1195064
  have htrace : WordTrace (prefixWord ++ tailWord_1195064) baseStart_1195064 baseEnd_1195064 := by
    simpa [prefixWord, tailWord_1195064, baseEnd_1195064] using wordTrace_append hprefix tailTrace_1195064
  have hstable : (prefixWord ++ tailWord_1195064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195064).length < 2 ^ (prefixWord ++ tailWord_1195064).sum := by decide
  have hdescent : baseEnd_1195064 < baseStart_1195064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195080 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_1195080 : Nat := 118140960795 + 1195080 * 2 ^ 59
def prefixEnd_1195080 : Nat := 4983230072969 + 3 ^ 40 * 1195080 * 2
def baseEnd_1195080 : Nat := 613650460575289477703933

theorem tailTrace_1195080 : CollatzResearch.WordTrace tailWord_1195080 prefixEnd_1195080 613650460575289477703933 := by
  unfold tailWord_1195080
  simp only [CollatzResearch.WordTrace]
  refine ⟨21794074255218369129803347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29058765673624492173071129 21794074255218369129803347)
  ·
    refine ⟨32691111382827553694705021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21794074255218369129803347 32691111382827553694705021)
    ·
      refine ⟨12259166768560332635514383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32691111382827553694705021 12259166768560332635514383)
      ·
        refine ⟨18388750152840498953271575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12259166768560332635514383 18388750152840498953271575)
        ·
          refine ⟨27583125229260748429907363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18388750152840498953271575 27583125229260748429907363)
          ·
            refine ⟨41374687843891122644861045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27583125229260748429907363 41374687843891122644861045)
            ·
              refine ⟨3878876985364792747955723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41374687843891122644861045 3878876985364792747955723)
              ·
                refine ⟨5818315478047189121933585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878876985364792747955723 5818315478047189121933585)
                ·
                  refine ⟨4363736608535391841450189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5818315478047189121933585 4363736608535391841450189)
                  ·
                    refine ⟨1636401228200771940543821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4363736608535391841450189 1636401228200771940543821)
                    ·
                      refine ⟨613650460575289477703933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1636401228200771940543821 613650460575289477703933)
                      ·
                        rfl

theorem cell23_1195080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_1195080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195080 prefixEnd_1195080 := by exact prefixLift 1195080
  have htrace : WordTrace (prefixWord ++ tailWord_1195080) baseStart_1195080 baseEnd_1195080 := by
    simpa [prefixWord, tailWord_1195080, baseEnd_1195080] using wordTrace_append hprefix tailTrace_1195080
  have hstable : (prefixWord ++ tailWord_1195080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195080).length < 2 ^ (prefixWord ++ tailWord_1195080).sum := by decide
  have hdescent : baseEnd_1195080 < baseStart_1195080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195100 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1195100 : Nat := 118140960795 + 1195100 * 2 ^ 59
def prefixEnd_1195100 : Nat := 4983230072969 + 3 ^ 40 * 1195100 * 2
def baseEnd_1195100 : Nat := 204553576729459799817947

theorem tailTrace_1195100 : CollatzResearch.WordTrace tailWord_1195100 prefixEnd_1195100 204553576729459799817947 := by
  unfold tailWord_1195100
  simp only [CollatzResearch.WordTrace]
  refine ⟨21794438985182140837667377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29059251980242854450223169 21794438985182140837667377)
  ·
    refine ⟨16345829238886605628250533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21794438985182140837667377 16345829238886605628250533)
    ·
      refine ⟨3064842982291238555296975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16345829238886605628250533 3064842982291238555296975)
      ·
        refine ⟨4597264473436857832945463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3064842982291238555296975 4597264473436857832945463)
        ·
          refine ⟨6895896710155286749418195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597264473436857832945463 6895896710155286749418195)
          ·
            refine ⟨10343845065232930124127293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895896710155286749418195 10343845065232930124127293)
            ·
              refine ⟨3878941899462348796547735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10343845065232930124127293 3878941899462348796547735)
              ·
                refine ⟨5818412849193523194821603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3878941899462348796547735 5818412849193523194821603)
                ·
                  refine ⟨8727619273790284792232405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5818412849193523194821603 8727619273790284792232405)
                  ·
                    refine ⟨204553576729459799817947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8727619273790284792232405 204553576729459799817947)
                    ·
                      rfl

theorem cell23_1195100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1195100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195100 prefixEnd_1195100 := by exact prefixLift 1195100
  have htrace : WordTrace (prefixWord ++ tailWord_1195100) baseStart_1195100 baseEnd_1195100 := by
    simpa [prefixWord, tailWord_1195100, baseEnd_1195100] using wordTrace_append hprefix tailTrace_1195100
  have hstable : (prefixWord ++ tailWord_1195100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195100).length < 2 ^ (prefixWord ++ tailWord_1195100).sum := by decide
  have hdescent : baseEnd_1195100 < baseStart_1195100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195120 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_1195120 : Nat := 118140960795 + 1195120 * 2 ^ 59
def prefixEnd_1195120 : Nat := 4983230072969 + 3 ^ 40 * 1195120 * 2
def baseEnd_1195120 : Nat := 613670999801469321203749

theorem tailTrace_1195120 : CollatzResearch.WordTrace tailWord_1195120 prefixEnd_1195120 613670999801469321203749 := by
  unfold tailWord_1195120
  simp only [CollatzResearch.WordTrace]
  refine ⟨21794803715145912545531407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29059738286861216727375209 21794803715145912545531407)
  ·
    refine ⟨32692205572718868818297111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21794803715145912545531407 32692205572718868818297111)
    ·
      refine ⟨49038308359078303227445667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32692205572718868818297111 49038308359078303227445667)
      ·
        refine ⟨73557462538617454841168501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49038308359078303227445667 73557462538617454841168501)
        ·
          refine ⟨6896012112995386391359547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73557462538617454841168501 6896012112995386391359547)
          ·
            refine ⟨10344018169493079587039321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896012112995386391359547 10344018169493079587039321)
            ·
              refine ⟨7758013627119809690279491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10344018169493079587039321 7758013627119809690279491)
              ·
                refine ⟨11637020440679714535419237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7758013627119809690279491 11637020440679714535419237)
                ·
                  refine ⟨2181941332627446475391107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11637020440679714535419237 2181941332627446475391107)
                  ·
                    refine ⟨3272911998941169713086661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2181941332627446475391107 3272911998941169713086661)
                    ·
                      refine ⟨613670999801469321203749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3272911998941169713086661 613670999801469321203749)
                      ·
                        rfl

theorem cell23_1195120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_1195120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195120 prefixEnd_1195120 := by exact prefixLift 1195120
  have htrace : WordTrace (prefixWord ++ tailWord_1195120) baseStart_1195120 baseEnd_1195120 := by
    simpa [prefixWord, tailWord_1195120, baseEnd_1195120] using wordTrace_append hprefix tailTrace_1195120
  have hstable : (prefixWord ++ tailWord_1195120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195120).length < 2 ^ (prefixWord ++ tailWord_1195120).sum := by decide
  have hdescent : baseEnd_1195120 < baseStart_1195120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195153 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_1195153 : Nat := 118140960795 + 1195153 * 2 ^ 59
def prefixEnd_1195153 : Nat := 4983230072969 + 3 ^ 40 * 1195153 * 2
def baseEnd_1195153 : Nat := 613687944663067692091097

theorem tailTrace_1195153 : CollatzResearch.WordTrace tailWord_1195153 prefixEnd_1195153 613687944663067692091097 := by
  unfold tailWord_1195153
  simp only [CollatzResearch.WordTrace]
  refine ⟨43590811039172271727014113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29060540692781514484676075 43590811039172271727014113)
  ·
    refine ⟨32693108279379203795260585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43590811039172271727014113 32693108279379203795260585)
    ·
      refine ⟨24519831209534402846445439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32693108279379203795260585 24519831209534402846445439)
      ·
        refine ⟨36779746814301604269668159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24519831209534402846445439 36779746814301604269668159)
        ·
          refine ⟨55169620221452406404502239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36779746814301604269668159 55169620221452406404502239)
          ·
            refine ⟨82754430332178609606753359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55169620221452406404502239 82754430332178609606753359)
            ·
              refine ⟨124131645498267914410130039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82754430332178609606753359 124131645498267914410130039)
              ·
                refine ⟨186197468247401871615195059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124131645498267914410130039 186197468247401871615195059)
                ·
                  refine ⟨279296202371102807422792589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186197468247401871615195059 279296202371102807422792589)
                  ·
                    refine ⟨104736075889163552783547221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279296202371102807422792589 104736075889163552783547221)
                    ·
                      refine ⟨613687944663067692091097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 104736075889163552783547221 613687944663067692091097)
                      ·
                        rfl

theorem cell23_1195153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_1195153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195153 prefixEnd_1195153 := by exact prefixLift 1195153
  have htrace : WordTrace (prefixWord ++ tailWord_1195153) baseStart_1195153 baseEnd_1195153 := by
    simpa [prefixWord, tailWord_1195153, baseEnd_1195153] using wordTrace_append hprefix tailTrace_1195153
  have hstable : (prefixWord ++ tailWord_1195153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195153).length < 2 ^ (prefixWord ++ tailWord_1195153).sum := by decide
  have hdescent : baseEnd_1195153 < baseStart_1195153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195160 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 8]
def baseStart_1195160 : Nat := 118140960795 + 1195160 * 2 ^ 59
def prefixEnd_1195160 : Nat := 4983230072969 + 3 ^ 40 * 1195160 * 2
def baseEnd_1195160 : Nat := 68187948780849907189285

theorem tailTrace_1195160 : CollatzResearch.WordTrace tailWord_1195160 prefixEnd_1195160 68187948780849907189285 := by
  unfold tailWord_1195160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795533175073455961259467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29060710900097941281679289 21795533175073455961259467)
  ·
    refine ⟨32693299762610183941889201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21795533175073455961259467 32693299762610183941889201)
    ·
      refine ⟨24519974821957637956416901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32693299762610183941889201 24519974821957637956416901)
      ·
        refine ⟨4597495279117057116828169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24519974821957637956416901 4597495279117057116828169)
        ·
          refine ⟨3448121459337792837621127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4597495279117057116828169 3448121459337792837621127)
          ·
            refine ⟨5172182189006689256431691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448121459337792837621127 5172182189006689256431691)
            ·
              refine ⟨7758273283510033884647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172182189006689256431691 7758273283510033884647537)
              ·
                refine ⟨5818704962632525413485653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7758273283510033884647537 5818704962632525413485653)
                ·
                  refine ⟨68187948780849907189285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5818704962632525413485653 68187948780849907189285)
                  ·
                    rfl

theorem cell23_1195160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_1195160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195160 prefixEnd_1195160 := by exact prefixLift 1195160
  have htrace : WordTrace (prefixWord ++ tailWord_1195160) baseStart_1195160 baseEnd_1195160 := by
    simpa [prefixWord, tailWord_1195160, baseEnd_1195160] using wordTrace_append hprefix tailTrace_1195160
  have hstable : (prefixWord ++ tailWord_1195160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195160).length < 2 ^ (prefixWord ++ tailWord_1195160).sum := by decide
  have hdescent : baseEnd_1195160 < baseStart_1195160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195163 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_1195163 : Nat := 118140960795 + 1195163 * 2 ^ 59
def prefixEnd_1195163 : Nat := 4983230072969 + 3 ^ 40 * 1195163 * 2
def baseEnd_1195163 : Nat := 613693079469612652966051

theorem tailTrace_1195163 : CollatzResearch.WordTrace tailWord_1195163 prefixEnd_1195163 613693079469612652966051 := by
  unfold tailWord_1195163
  simp only [CollatzResearch.WordTrace]
  refine ⟨43591175769136043434878143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29060783846090695623252095 43591175769136043434878143)
  ·
    refine ⟨65386763653704065152317215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43591175769136043434878143 65386763653704065152317215)
    ·
      refine ⟨98080145480556097728475823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65386763653704065152317215 98080145480556097728475823)
      ·
        refine ⟨147120218220834146592713735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98080145480556097728475823 147120218220834146592713735)
        ·
          refine ⟨220680327331251219889070603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147120218220834146592713735 220680327331251219889070603)
          ·
            refine ⟨331020490996876829833605905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220680327331251219889070603 331020490996876829833605905)
            ·
              refine ⟨248265368247657622375204429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331020490996876829833605905 248265368247657622375204429)
              ·
                refine ⟨93099513092871608390701661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248265368247657622375204429 93099513092871608390701661)
                ·
                  refine ⟨34912317409826853146513123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93099513092871608390701661 34912317409826853146513123)
                  ·
                    refine ⟨52368476114740279719769685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34912317409826853146513123 52368476114740279719769685)
                    ·
                      refine ⟨613693079469612652966051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52368476114740279719769685 613693079469612652966051)
                      ·
                        rfl

theorem cell23_1195163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_1195163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195163 prefixEnd_1195163 := by exact prefixLift 1195163
  have htrace : WordTrace (prefixWord ++ tailWord_1195163) baseStart_1195163 baseEnd_1195163 := by
    simpa [prefixWord, tailWord_1195163, baseEnd_1195163] using wordTrace_append hprefix tailTrace_1195163
  have hstable : (prefixWord ++ tailWord_1195163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195163).length < 2 ^ (prefixWord ++ tailWord_1195163).sum := by decide
  have hdescent : baseEnd_1195163 < baseStart_1195163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195181 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1195181 : Nat := 118140960795 + 1195181 * 2 ^ 59
def prefixEnd_1195181 : Nat := 4983230072969 + 3 ^ 40 * 1195181 * 2
def baseEnd_1195181 : Nat := 204567440707131194180323

theorem tailTrace_1195181 : CollatzResearch.WordTrace tailWord_1195181 prefixEnd_1195181 204567440707131194180323 := by
  unfold tailWord_1195181
  simp only [CollatzResearch.WordTrace]
  refine ⟨43591832283070832509033397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29061221522047221672688931 43591832283070832509033397)
  ·
    refine ⟨4086734276537890547721881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43591832283070832509033397 4086734276537890547721881)
    ·
      refine ⟨3065050707403417910791411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4086734276537890547721881 3065050707403417910791411)
      ·
        refine ⟨4597576061105126866187117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065050707403417910791411 4597576061105126866187117)
        ·
          refine ⟨1724091022914422574820169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4597576061105126866187117 1724091022914422574820169)
          ·
            refine ⟨1293068267185816931115127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724091022914422574820169 1293068267185816931115127)
            ·
              refine ⟨1939602400778725396672691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293068267185816931115127 1939602400778725396672691)
              ·
                refine ⟨2909403601168088095009037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939602400778725396672691 2909403601168088095009037)
                ·
                  refine ⟨1091026350438033035628389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2909403601168088095009037 1091026350438033035628389)
                  ·
                    refine ⟨204567440707131194180323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1091026350438033035628389 204567440707131194180323)
                    ·
                      rfl

theorem cell23_1195181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1195181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195181 prefixEnd_1195181 := by exact prefixLift 1195181
  have htrace : WordTrace (prefixWord ++ tailWord_1195181) baseStart_1195181 baseEnd_1195181 := by
    simpa [prefixWord, tailWord_1195181, baseEnd_1195181] using wordTrace_append hprefix tailTrace_1195181
  have hstable : (prefixWord ++ tailWord_1195181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195181).length < 2 ^ (prefixWord ++ tailWord_1195181).sum := by decide
  have hdescent : baseEnd_1195181 < baseStart_1195181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195197 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_1195197 : Nat := 118140960795 + 1195197 * 2 ^ 59
def prefixEnd_1195197 : Nat := 4983230072969 + 3 ^ 40 * 1195197 * 2
def baseEnd_1195197 : Nat := 613710537811865519940895

theorem tailTrace_1195197 : CollatzResearch.WordTrace tailWord_1195197 prefixEnd_1195197 613710537811865519940895 := by
  unfold tailWord_1195197
  simp only [CollatzResearch.WordTrace]
  refine ⟨43592415851012867241615845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29061610567341911494410563 43592415851012867241615845)
  ·
    refine ⟨8173577972064912607802971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43592415851012867241615845 8173577972064912607802971)
    ·
      refine ⟨12260366958097368911704457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8173577972064912607802971 12260366958097368911704457)
      ·
        refine ⟨9195275218573026683778343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12260366958097368911704457 9195275218573026683778343)
        ·
          refine ⟨13792912827859540025667515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195275218573026683778343 13792912827859540025667515)
          ·
            refine ⟨20689369241789310038501273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13792912827859540025667515 20689369241789310038501273)
            ·
              refine ⟨15517026931341982528875955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20689369241789310038501273 15517026931341982528875955)
              ·
                refine ⟨23275540397012973793313933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15517026931341982528875955 23275540397012973793313933)
                ·
                  refine ⟨8728327648879865172492725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23275540397012973793313933 8728327648879865172492725)
                  ·
                    refine ⟨818280717082487359921193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8728327648879865172492725 818280717082487359921193)
                    ·
                      refine ⟨613710537811865519940895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818280717082487359921193 613710537811865519940895)
                      ·
                        rfl

theorem cell23_1195197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_1195197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195197 prefixEnd_1195197 := by exact prefixLift 1195197
  have htrace : WordTrace (prefixWord ++ tailWord_1195197) baseStart_1195197 baseEnd_1195197 := by
    simpa [prefixWord, tailWord_1195197, baseEnd_1195197] using wordTrace_append hprefix tailTrace_1195197
  have hstable : (prefixWord ++ tailWord_1195197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195197).length < 2 ^ (prefixWord ++ tailWord_1195197).sum := by decide
  have hdescent : baseEnd_1195197 < baseStart_1195197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195257 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1195257 : Nat := 118140960795 + 1195257 * 2 ^ 59
def prefixEnd_1195257 : Nat := 4983230072969 + 3 ^ 40 * 1195257 * 2
def baseEnd_1195257 : Nat := 613741346651135285190619

theorem tailTrace_1195257 : CollatzResearch.WordTrace tailWord_1195257 prefixEnd_1195257 613741346651135285190619 := by
  unfold tailWord_1195257
  simp only [CollatzResearch.WordTrace]
  refine ⟨43594604230795497488800025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29063069487196998325866683 43594604230795497488800025)
  ·
    refine ⟨32695953173096623116600019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43594604230795497488800025 32695953173096623116600019)
    ·
      refine ⟨49043929759644934674900029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32695953173096623116600019 49043929759644934674900029)
      ·
        refine ⟨18391473659866850503087511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49043929759644934674900029 18391473659866850503087511)
        ·
          refine ⟨27587210489800275754631267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18391473659866850503087511 27587210489800275754631267)
          ·
            refine ⟨41380815734700413631946901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27587210489800275754631267 41380815734700413631946901)
            ·
              refine ⟨1939725737564081888997511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41380815734700413631946901 1939725737564081888997511)
              ·
                refine ⟨2909588606346122833496267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939725737564081888997511 2909588606346122833496267)
                ·
                  refine ⟨4364382909519184250244401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2909588606346122833496267 4364382909519184250244401)
                  ·
                    refine ⟨3273287182139388187683301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4364382909519184250244401 3273287182139388187683301)
                    ·
                      refine ⟨613741346651135285190619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3273287182139388187683301 613741346651135285190619)
                      ·
                        rfl

theorem cell23_1195257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1195257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195257 prefixEnd_1195257 := by exact prefixLift 1195257
  have htrace : WordTrace (prefixWord ++ tailWord_1195257) baseStart_1195257 baseEnd_1195257 := by
    simpa [prefixWord, tailWord_1195257, baseEnd_1195257] using wordTrace_append hprefix tailTrace_1195257
  have hstable : (prefixWord ++ tailWord_1195257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195257).length < 2 ^ (prefixWord ++ tailWord_1195257).sum := by decide
  have hdescent : baseEnd_1195257 < baseStart_1195257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195267 : List Nat := [1, 1, 1, 3, 2, 5, 3, 7]
def baseStart_1195267 : Nat := 118140960795 + 1195267 * 2 ^ 59
def prefixEnd_1195267 : Nat := 4983230072969 + 3 ^ 40 * 1195267 * 2
def baseEnd_1195267 : Nat := 22731351165099268372799

theorem tailTrace_1195267 : CollatzResearch.WordTrace tailWord_1195267 prefixEnd_1195267 22731351165099268372799 := by
  unfold tailWord_1195267
  simp only [CollatzResearch.WordTrace]
  refine ⟨43594968960759269196664055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29063312640506179464442703 43594968960759269196664055)
  ·
    refine ⟨65392453441138903794996083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43594968960759269196664055 65392453441138903794996083)
    ·
      refine ⟨98088680161708355692494125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65392453441138903794996083 98088680161708355692494125)
      ·
        refine ⟨36783255060640633384685297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98088680161708355692494125 36783255060640633384685297)
        ·
          refine ⟨27587441295480475038513973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36783255060640633384685297 27587441295480475038513973)
          ·
            refine ⟨2586322621451294534860685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27587441295480475038513973 2586322621451294534860685)
            ·
              refine ⟨969870983044235450572757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2586322621451294534860685 969870983044235450572757)
              ·
                refine ⟨22731351165099268372799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 969870983044235450572757 22731351165099268372799)
                ·
                  rfl

theorem cell23_1195267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 7].length) (baseStart_1195267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195267 prefixEnd_1195267 := by exact prefixLift 1195267
  have htrace : WordTrace (prefixWord ++ tailWord_1195267) baseStart_1195267 baseEnd_1195267 := by
    simpa [prefixWord, tailWord_1195267, baseEnd_1195267] using wordTrace_append hprefix tailTrace_1195267
  have hstable : (prefixWord ++ tailWord_1195267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195267).length < 2 ^ (prefixWord ++ tailWord_1195267).sum := by decide
  have hdescent : baseEnd_1195267 < baseStart_1195267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195278 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1195278 : Nat := 118140960795 + 1195278 * 2 ^ 59
def prefixEnd_1195278 : Nat := 4983230072969 + 3 ^ 40 * 1195278 * 2
def baseEnd_1195278 : Nat := 613752129744879703028023

theorem tailTrace_1195278 : CollatzResearch.WordTrace tailWord_1195278 prefixEnd_1195278 613752129744879703028023 := by
  unfold tailWord_1195278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449421270464927259414311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29063580109146278716876325 5449421270464927259414311)
  ·
    refine ⟨8174131905697390889121467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449421270464927259414311 8174131905697390889121467)
    ·
      refine ⟨12261197858546086333682201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8174131905697390889121467 12261197858546086333682201)
      ·
        refine ⟨9195898393909564750261651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12261197858546086333682201 9195898393909564750261651)
        ·
          refine ⟨13793847590864347125392477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195898393909564750261651 13793847590864347125392477)
          ·
            refine ⟨5172692846574130172022179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13793847590864347125392477 5172692846574130172022179)
            ·
              refine ⟨7759039269861195258033269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5172692846574130172022179 7759039269861195258033269)
              ·
                refine ⟨727409931549487055440619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7759039269861195258033269 727409931549487055440619)
                ·
                  refine ⟨1091114897324230583160929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727409931549487055440619 1091114897324230583160929)
                  ·
                    refine ⟨818336172993172937370697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091114897324230583160929 818336172993172937370697)
                    ·
                      refine ⟨613752129744879703028023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818336172993172937370697 613752129744879703028023)
                      ·
                        rfl

theorem cell23_1195278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1195278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195278 prefixEnd_1195278 := by exact prefixLift 1195278
  have htrace : WordTrace (prefixWord ++ tailWord_1195278) baseStart_1195278 baseEnd_1195278 := by
    simpa [prefixWord, tailWord_1195278, baseEnd_1195278] using wordTrace_append hprefix tailTrace_1195278
  have hstable : (prefixWord ++ tailWord_1195278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195278).length < 2 ^ (prefixWord ++ tailWord_1195278).sum := by decide
  have hdescent : baseEnd_1195278 < baseStart_1195278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195318 : List Nat := [5, 1, 2, 3, 1, 2, 2, 7]
def baseStart_1195318 : Nat := 118140960795 + 1195318 * 2 ^ 59
def prefixEnd_1195318 : Nat := 4983230072969 + 3 ^ 40 * 1195318 * 2
def baseEnd_1195318 : Nat := 22732321073002205426957

theorem tailTrace_1195318 : CollatzResearch.WordTrace tailWord_1195318 prefixEnd_1195318 22732321073002205426957 := by
  unfold tailWord_1195318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724801817723406556673163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29064552722383003271180405 2724801817723406556673163)
  ·
    refine ⟨4087202726585109835009745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2724801817723406556673163 4087202726585109835009745)
    ·
      refine ⟨3065402044938832376257309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4087202726585109835009745 3065402044938832376257309)
      ·
        refine ⟨1149525766852062141096491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3065402044938832376257309 1149525766852062141096491)
        ·
          refine ⟨1724288650278093211644737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149525766852062141096491 1724288650278093211644737)
          ·
            refine ⟨1293216487708569908733553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724288650278093211644737 1293216487708569908733553)
            ·
              refine ⟨969912365781427431550165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293216487708569908733553 969912365781427431550165)
              ·
                refine ⟨22732321073002205426957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 969912365781427431550165 22732321073002205426957)
                ·
                  rfl

theorem cell23_1195318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_1195318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195318 prefixEnd_1195318 := by exact prefixLift 1195318
  have htrace : WordTrace (prefixWord ++ tailWord_1195318) baseStart_1195318 baseEnd_1195318 := by
    simpa [prefixWord, tailWord_1195318, baseEnd_1195318] using wordTrace_append hprefix tailTrace_1195318
  have hstable : (prefixWord ++ tailWord_1195318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195318).length < 2 ^ (prefixWord ++ tailWord_1195318).sum := by decide
  have hdescent : baseEnd_1195318 < baseStart_1195318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195351 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_1195351 : Nat := 118140960795 + 1195351 * 2 ^ 59
def prefixEnd_1195351 : Nat := 4983230072969 + 3 ^ 40 * 1195351 * 2
def baseEnd_1195351 : Nat := 613789613832657917415187

theorem tailTrace_1195351 : CollatzResearch.WordTrace tailWord_1195351 prefixEnd_1195351 613789613832657917415187 := by
  unfold tailWord_1195351
  simp only [CollatzResearch.WordTrace]
  refine ⟨43598032692454951542721907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29065355128303301028481271 43598032692454951542721907)
  ·
    refine ⟨65397049038682427314082861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43598032692454951542721907 65397049038682427314082861)
    ·
      refine ⟨24523893389505910242781073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65397049038682427314082861 24523893389505910242781073)
      ·
        refine ⟨18392920042129432682085805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24523893389505910242781073 18392920042129432682085805)
        ·
          refine ⟨6897345015798537255782177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18392920042129432682085805 6897345015798537255782177)
          ·
            refine ⟨5173008761848902941836633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6897345015798537255782177 5173008761848902941836633)
            ·
              refine ⟨3879756571386677206377475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5173008761848902941836633 3879756571386677206377475)
              ·
                refine ⟨5819634857080015809566213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879756571386677206377475 5819634857080015809566213)
                ·
                  refine ⟨1091181535702502964293665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5819634857080015809566213 1091181535702502964293665)
                  ·
                    refine ⟨818386151776877223220249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091181535702502964293665 818386151776877223220249)
                    ·
                      refine ⟨613789613832657917415187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818386151776877223220249 613789613832657917415187)
                      ·
                        rfl

theorem cell23_1195351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_1195351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195351 prefixEnd_1195351 := by exact prefixLift 1195351
  have htrace : WordTrace (prefixWord ++ tailWord_1195351) baseStart_1195351 baseEnd_1195351 := by
    simpa [prefixWord, tailWord_1195351, baseEnd_1195351] using wordTrace_append hprefix tailTrace_1195351
  have hstable : (prefixWord ++ tailWord_1195351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195351).length < 2 ^ (prefixWord ++ tailWord_1195351).sum := by decide
  have hdescent : baseEnd_1195351 < baseStart_1195351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195397 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_1195397 : Nat := 118140960795 + 1195397 * 2 ^ 59
def prefixEnd_1195397 : Nat := 4983230072969 + 3 ^ 40 * 1195397 * 2
def baseEnd_1195397 : Nat := 613813233942764737439975

theorem tailTrace_1195397 : CollatzResearch.WordTrace tailWord_1195397 prefixEnd_1195397 613813233942764737439975 := by
  unfold tailWord_1195397
  simp only [CollatzResearch.WordTrace]
  refine ⟨43599710450288301398896445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29066473633525534265930963 43599710450288301398896445)
  ·
    refine ⟨16349891418858113024586167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43599710450288301398896445 16349891418858113024586167)
    ·
      refine ⟨24524837128287169536879251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16349891418858113024586167 24524837128287169536879251)
      ·
        refine ⟨36787255692430754305318877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24524837128287169536879251 36787255692430754305318877)
        ·
          refine ⟨13795220884661532864494579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36787255692430754305318877 13795220884661532864494579)
          ·
            refine ⟨20692831326992299296741869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13795220884661532864494579 20692831326992299296741869)
            ·
              refine ⟨7759811747622112236278201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20692831326992299296741869 7759811747622112236278201)
              ·
                refine ⟨5819858810716584177208651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7759811747622112236278201 5819858810716584177208651)
                ·
                  refine ⟨8729788216074876265812977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5819858810716584177208651 8729788216074876265812977)
                  ·
                    refine ⟨6547341162056157199359733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8729788216074876265812977 6547341162056157199359733)
                    ·
                      refine ⟨613813233942764737439975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6547341162056157199359733 613813233942764737439975)
                      ·
                        rfl

theorem cell23_1195397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_1195397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195397 prefixEnd_1195397 := by exact prefixLift 1195397
  have htrace : WordTrace (prefixWord ++ tailWord_1195397) baseStart_1195397 baseEnd_1195397 := by
    simpa [prefixWord, tailWord_1195397, baseEnd_1195397] using wordTrace_append hprefix tailTrace_1195397
  have hstable : (prefixWord ++ tailWord_1195397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195397).length < 2 ^ (prefixWord ++ tailWord_1195397).sum := by decide
  have hdescent : baseEnd_1195397 < baseStart_1195397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195447 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 8]
def baseStart_1195447 : Nat := 118140960795 + 1195447 * 2 ^ 59
def prefixEnd_1195447 : Nat := 4983230072969 + 3 ^ 40 * 1195447 * 2
def baseEnd_1195447 : Nat := 68204323108387726868305

theorem tailTrace_1195447 : CollatzResearch.WordTrace tailWord_1195447 prefixEnd_1195447 68204323108387726868305 := by
  unfold tailWord_1195447
  simp only [CollatzResearch.WordTrace]
  refine ⟨43601534100107159938216595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29067689400071439958811063 43601534100107159938216595)
  ·
    refine ⟨65402301150160739907324893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43601534100107159938216595 65402301150160739907324893)
    ·
      refine ⟨24525862931310277465246835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65402301150160739907324893 24525862931310277465246835)
      ·
        refine ⟨36788794396965416197870253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24525862931310277465246835 36788794396965416197870253)
        ·
          refine ⟨13795797898862031074201345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36788794396965416197870253 13795797898862031074201345)
          ·
            refine ⟨10346848424146523305651009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13795797898862031074201345 10346848424146523305651009)
            ·
              refine ⟨7760136318109892479238257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10346848424146523305651009 7760136318109892479238257)
              ·
                refine ⟨5820102238582419359428693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7760136318109892479238257 5820102238582419359428693)
                ·
                  refine ⟨68204323108387726868305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5820102238582419359428693 68204323108387726868305)
                  ·
                    rfl

theorem cell23_1195447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 8].length) (baseStart_1195447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195447 prefixEnd_1195447 := by exact prefixLift 1195447
  have htrace : WordTrace (prefixWord ++ tailWord_1195447) baseStart_1195447 baseEnd_1195447 := by
    simpa [prefixWord, tailWord_1195447, baseEnd_1195447] using wordTrace_append hprefix tailTrace_1195447
  have hstable : (prefixWord ++ tailWord_1195447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195447).length < 2 ^ (prefixWord ++ tailWord_1195447).sum := by decide
  have hdescent : baseEnd_1195447 < baseStart_1195447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195467 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_1195467 : Nat := 118140960795 + 1195467 * 2 ^ 59
def prefixEnd_1195467 : Nat := 4983230072969 + 3 ^ 40 * 1195467 * 2
def baseEnd_1195467 : Nat := 613849177588579463564653

theorem tailTrace_1195467 : CollatzResearch.WordTrace tailWord_1195467 prefixEnd_1195467 613849177588579463564653 := by
  unfold tailWord_1195467
  simp only [CollatzResearch.WordTrace]
  refine ⟨43602263560034703353944655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29068175706689802235963103 43602263560034703353944655)
  ·
    refine ⟨65403395340052055030916983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43602263560034703353944655 65403395340052055030916983)
    ·
      refine ⟨98105093010078082546375475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65403395340052055030916983 98105093010078082546375475)
      ·
        refine ⟨147157639515117123819563213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98105093010078082546375475 147157639515117123819563213)
        ·
          refine ⟨55184114818168921432336205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147157639515117123819563213 55184114818168921432336205)
          ·
            refine ⟨20694043056813345537126077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55184114818168921432336205 20694043056813345537126077)
            ·
              refine ⟨7760266146305004576422279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20694043056813345537126077 7760266146305004576422279)
              ·
                refine ⟨11640399219457506864633419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760266146305004576422279 11640399219457506864633419)
                ·
                  refine ⟨17460598829186260296950129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11640399219457506864633419 17460598829186260296950129)
                  ·
                    refine ⟨13095449121889695222712597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17460598829186260296950129 13095449121889695222712597)
                    ·
                      refine ⟨613849177588579463564653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13095449121889695222712597 613849177588579463564653)
                      ·
                        rfl

theorem cell23_1195467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_1195467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195467 prefixEnd_1195467 := by exact prefixLift 1195467
  have htrace : WordTrace (prefixWord ++ tailWord_1195467) baseStart_1195467 baseEnd_1195467 := by
    simpa [prefixWord, tailWord_1195467, baseEnd_1195467] using wordTrace_append hprefix tailTrace_1195467
  have hstable : (prefixWord ++ tailWord_1195467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195467).length < 2 ^ (prefixWord ++ tailWord_1195467).sum := by decide
  have hdescent : baseEnd_1195467 < baseStart_1195467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195468 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_1195468 : Nat := 118140960795 + 1195468 * 2 ^ 59
def prefixEnd_1195468 : Nat := 4983230072969 + 3 ^ 40 * 1195468 * 2
def baseEnd_1195468 : Nat := 204616563689744653217383

theorem tailTrace_1195468 : CollatzResearch.WordTrace tailWord_1195468 prefixEnd_1195468 204616563689744653217383 := by
  unfold tailWord_1195468
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801150016515540262365529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29068200022020720349820705 21801150016515540262365529)
  ·
    refine ⟨16350862512386655196774147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21801150016515540262365529 16350862512386655196774147)
    ·
      refine ⟨24526293768579982795161221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16350862512386655196774147 24526293768579982795161221)
      ·
        refine ⟨4598680081608746774092729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24526293768579982795161221 4598680081608746774092729)
        ·
          refine ⟨3449010061206560080569547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598680081608746774092729 3449010061206560080569547)
          ·
            refine ⟨5173515091809840120854321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449010061206560080569547 5173515091809840120854321)
            ·
              refine ⟨3880136318857380090640741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5173515091809840120854321 3880136318857380090640741)
              ·
                refine ⟨727525559785758766995139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3880136318857380090640741 727525559785758766995139)
                ·
                  refine ⟨1091288339678638150492709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727525559785758766995139 1091288339678638150492709)
                  ·
                    refine ⟨204616563689744653217383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1091288339678638150492709 204616563689744653217383)
                    ·
                      rfl

theorem cell23_1195468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_1195468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195468 prefixEnd_1195468 := by exact prefixLift 1195468
  have htrace : WordTrace (prefixWord ++ tailWord_1195468) baseStart_1195468 baseEnd_1195468 := by
    simpa [prefixWord, tailWord_1195468, baseEnd_1195468] using wordTrace_append hprefix tailTrace_1195468
  have hstable : (prefixWord ++ tailWord_1195468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195468).length < 2 ^ (prefixWord ++ tailWord_1195468).sum := by decide
  have hdescent : baseEnd_1195468 < baseStart_1195468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195481 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 6]
def baseStart_1195481 : Nat := 118140960795 + 1195481 * 2 ^ 59
def prefixEnd_1195481 : Nat := 4983230072969 + 3 ^ 40 * 1195481 * 2
def baseEnd_1195481 : Nat := 68206262924193600976621

theorem tailTrace_1195481 : CollatzResearch.WordTrace tailWord_1195481 prefixEnd_1195481 68206262924193600976621 := by
  unfold tailWord_1195481
  simp only [CollatzResearch.WordTrace]
  refine ⟨43602774181983983744954297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29068516121322655829969531 43602774181983983744954297)
  ·
    refine ⟨32702080636487987808715723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43602774181983983744954297 32702080636487987808715723)
    ·
      refine ⟨49053120954731981713073585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32702080636487987808715723 49053120954731981713073585)
      ·
        refine ⟨36789840716048986284805189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49053120954731981713073585 36789840716048986284805189)
        ·
          refine ⟨6898095134259184928400973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36789840716048986284805189 6898095134259184928400973)
          ·
            refine ⟨2586785675347194348150365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6898095134259184928400973 2586785675347194348150365)
            ·
              refine ⟨970044628255197880556387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2586785675347194348150365 970044628255197880556387)
              ·
                refine ⟨1455066942382796820834581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970044628255197880556387 1455066942382796820834581)
                ·
                  refine ⟨68206262924193600976621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1455066942382796820834581 68206262924193600976621)
                  ·
                    rfl

theorem cell23_1195481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 6].length) (baseStart_1195481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195481 prefixEnd_1195481 := by exact prefixLift 1195481
  have htrace : WordTrace (prefixWord ++ tailWord_1195481) baseStart_1195481 baseEnd_1195481 := by
    simpa [prefixWord, tailWord_1195481, baseEnd_1195481] using wordTrace_append hprefix tailTrace_1195481
  have hstable : (prefixWord ++ tailWord_1195481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195481).length < 2 ^ (prefixWord ++ tailWord_1195481).sum := by decide
  have hdescent : baseEnd_1195481 < baseStart_1195481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195548 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1195548 : Nat := 118140960795 + 1195548 * 2 ^ 59
def prefixEnd_1195548 : Nat := 4983230072969 + 3 ^ 40 * 1195548 * 2
def baseEnd_1195548 : Nat := 613890769521593646651781

theorem tailTrace_1195548 : CollatzResearch.WordTrace tailWord_1195548 prefixEnd_1195548 613890769521593646651781 := by
  unfold tailWord_1195548
  simp only [CollatzResearch.WordTrace]
  refine ⟨21802608936370627093821649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29070145248494169458428865 21802608936370627093821649)
  ·
    refine ⟨16351956702277970320366237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21802608936370627093821649 16351956702277970320366237)
    ·
      refine ⟨6131983763354238870137339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16351956702277970320366237 6131983763354238870137339)
      ·
        refine ⟨9197975645031358305206009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131983763354238870137339 9197975645031358305206009)
        ·
          refine ⟨6898481733773518728904507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9197975645031358305206009 6898481733773518728904507)
          ·
            refine ⟨10347722600660278093356761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6898481733773518728904507 10347722600660278093356761)
            ·
              refine ⟨7760791950495208570017571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10347722600660278093356761 7760791950495208570017571)
              ·
                refine ⟨11641187925742812855026357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7760791950495208570017571 11641187925742812855026357)
                ·
                  refine ⟨1091361368038388705158721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11641187925742812855026357 1091361368038388705158721)
                  ·
                    refine ⟨818521026028791528869041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091361368038388705158721 818521026028791528869041)
                    ·
                      refine ⟨613890769521593646651781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818521026028791528869041 613890769521593646651781)
                      ·
                        rfl

theorem cell23_1195548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1195548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195548 prefixEnd_1195548 := by exact prefixLift 1195548
  have htrace : WordTrace (prefixWord ++ tailWord_1195548) baseStart_1195548 baseEnd_1195548 := by
    simpa [prefixWord, tailWord_1195548, baseEnd_1195548] using wordTrace_append hprefix tailTrace_1195548
  have hstable : (prefixWord ++ tailWord_1195548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195548).length < 2 ^ (prefixWord ++ tailWord_1195548).sum := by decide
  have hdescent : baseEnd_1195548 < baseStart_1195548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195554 : List Nat := [3, 3, 1, 1, 1, 1, 4, 9]
def baseStart_1195554 : Nat := 118140960795 + 1195554 * 2 ^ 59
def prefixEnd_1195554 : Nat := 4983230072969 + 3 ^ 40 * 1195554 * 2
def baseEnd_1195554 : Nat := 22736809274278541599139

theorem tailTrace_1195554 : CollatzResearch.WordTrace tailWord_1195554 prefixEnd_1195554 22736809274278541599139 := by
  unfold tailWord_1195554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901359177679879303090429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29070291140479678141574477 10901359177679879303090429)
  ·
    refine ⟨4088009691629954738658911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10901359177679879303090429 4088009691629954738658911)
    ·
      refine ⟨6132014537444932107988367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088009691629954738658911 6132014537444932107988367)
      ·
        refine ⟨9198021806167398161982551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6132014537444932107988367 9198021806167398161982551)
        ·
          refine ⟨13797032709251097242973827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9198021806167398161982551 13797032709251097242973827)
          ·
            refine ⟨20695549063876645864460741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13797032709251097242973827 20695549063876645864460741)
            ·
              refine ⟨3880415449476871099586389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20695549063876645864460741 3880415449476871099586389)
              ·
                refine ⟨22736809274278541599139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3880415449476871099586389 22736809274278541599139)
                ·
                  rfl

theorem cell23_1195554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_1195554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195554 prefixEnd_1195554 := by exact prefixLift 1195554
  have htrace : WordTrace (prefixWord ++ tailWord_1195554) baseStart_1195554 baseEnd_1195554 := by
    simpa [prefixWord, tailWord_1195554, baseEnd_1195554] using wordTrace_append hprefix tailTrace_1195554
  have hstable : (prefixWord ++ tailWord_1195554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195554).length < 2 ^ (prefixWord ++ tailWord_1195554).sum := by decide
  have hdescent : baseEnd_1195554 < baseStart_1195554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195608 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_1195608 : Nat := 118140960795 + 1195608 * 2 ^ 59
def prefixEnd_1195608 : Nat := 4983230072969 + 3 ^ 40 * 1195608 * 2
def baseEnd_1195608 : Nat := 613921578360863411901505

theorem tailTrace_1195608 : CollatzResearch.WordTrace tailWord_1195608 prefixEnd_1195608 613921578360863411901505 := by
  unfold tailWord_1195608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21803703126261942217413739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29071604168349256289884985 21803703126261942217413739)
  ·
    refine ⟨32705554689392913326120609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21803703126261942217413739 32705554689392913326120609)
    ·
      refine ⟨24529166017044684994590457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32705554689392913326120609 24529166017044684994590457)
      ·
        refine ⟨18396874512783513745942843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24529166017044684994590457 18396874512783513745942843)
        ·
          refine ⟨27595311769175270618914265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18396874512783513745942843 27595311769175270618914265)
          ·
            refine ⟨20696483826881452964185699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27595311769175270618914265 20696483826881452964185699)
            ·
              refine ⟨31044725740322179446278549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20696483826881452964185699 31044725740322179446278549)
              ·
                refine ⟨1455221519077602161544307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31044725740322179446278549 1455221519077602161544307)
                ·
                  refine ⟨2182832278616403242316461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455221519077602161544307 2182832278616403242316461)
                  ·
                    refine ⟨818562104481151215868673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182832278616403242316461 818562104481151215868673)
                    ·
                      refine ⟨613921578360863411901505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818562104481151215868673 613921578360863411901505)
                      ·
                        rfl

theorem cell23_1195608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_1195608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195608 prefixEnd_1195608 := by exact prefixLift 1195608
  have htrace : WordTrace (prefixWord ++ tailWord_1195608) baseStart_1195608 baseEnd_1195608 := by
    simpa [prefixWord, tailWord_1195608, baseEnd_1195608] using wordTrace_append hprefix tailTrace_1195608
  have hstable : (prefixWord ++ tailWord_1195608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195608).length < 2 ^ (prefixWord ++ tailWord_1195608).sum := by decide
  have hdescent : baseEnd_1195608 < baseStart_1195608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195625 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 1, 3, 2]
def baseStart_1195625 : Nat := 118140960795 + 1195625 * 2 ^ 59
def prefixEnd_1195625 : Nat := 4983230072969 + 3 ^ 40 * 1195625 * 2
def baseEnd_1195625 : Nat := 613930307531989845388927

theorem tailTrace_1195625 : CollatzResearch.WordTrace tailWord_1195625 prefixEnd_1195625 613930307531989845388927 := by
  unfold tailWord_1195625
  simp only [CollatzResearch.WordTrace]
  refine ⟨43608026293462296338196329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29072017528974864225464219 43608026293462296338196329)
  ·
    refine ⟨32706019720096722253647247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43608026293462296338196329 32706019720096722253647247)
    ·
      refine ⟨49059029580145083380470871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32706019720096722253647247 49059029580145083380470871)
      ·
        refine ⟨73588544370217625070706307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49059029580145083380470871 73588544370217625070706307)
        ·
          refine ⟨110382816555326437606059461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73588544370217625070706307 110382816555326437606059461)
          ·
            refine ⟨20696778104123707051136149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110382816555326437606059461 20696778104123707051136149)
            ·
              refine ⟨970161473630798768022007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20696778104123707051136149 970161473630798768022007)
              ·
                refine ⟨1455242210446198152033011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970161473630798768022007 1455242210446198152033011)
                ·
                  refine ⟨2182863315669297228049517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455242210446198152033011 2182863315669297228049517)
                  ·
                    refine ⟨818573743375986460518569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2182863315669297228049517 818573743375986460518569)
                    ·
                      refine ⟨613930307531989845388927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818573743375986460518569 613930307531989845388927)
                      ·
                        rfl

theorem cell23_1195625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 3, 2].length) (baseStart_1195625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195625 prefixEnd_1195625 := by exact prefixLift 1195625
  have htrace : WordTrace (prefixWord ++ tailWord_1195625) baseStart_1195625 baseEnd_1195625 := by
    simpa [prefixWord, tailWord_1195625, baseEnd_1195625] using wordTrace_append hprefix tailTrace_1195625
  have hstable : (prefixWord ++ tailWord_1195625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195625).length < 2 ^ (prefixWord ++ tailWord_1195625).sum := by decide
  have hdescent : baseEnd_1195625 < baseStart_1195625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195655 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_1195655 : Nat := 118140960795 + 1195655 * 2 ^ 59
def prefixEnd_1195655 : Nat := 4983230072969 + 3 ^ 40 * 1195655 * 2
def baseEnd_1195655 : Nat := 613945711951624728013789

theorem tailTrace_1195655 : CollatzResearch.WordTrace tailWord_1195655 prefixEnd_1195655 613945711951624728013789 := by
  unfold tailWord_1195655
  simp only [CollatzResearch.WordTrace]
  refine ⟨43609120483353611461788419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29072746988902407641192279 43609120483353611461788419)
  ·
    refine ⟨65413680725030417192682629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43609120483353611461788419 65413680725030417192682629)
    ·
      refine ⟨12265065135943203223627993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65413680725030417192682629 12265065135943203223627993)
      ·
        refine ⟨9198798851957402417720995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12265065135943203223627993 9198798851957402417720995)
        ·
          refine ⟨13798198277936103626581493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9198798851957402417720995 13798198277936103626581493)
          ·
            refine ⟨1293581088556509714992015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13798198277936103626581493 1293581088556509714992015)
            ·
              refine ⟨1940371632834764572488023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293581088556509714992015 1940371632834764572488023)
              ·
                refine ⟨2910557449252146858732035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940371632834764572488023 2910557449252146858732035)
                ·
                  refine ⟨4365836173878220288098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2910557449252146858732035 4365836173878220288098053)
                  ·
                    refine ⟨818594282602166304018385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4365836173878220288098053 818594282602166304018385)
                    ·
                      refine ⟨613945711951624728013789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818594282602166304018385 613945711951624728013789)
                      ·
                        rfl

theorem cell23_1195655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_1195655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195655 prefixEnd_1195655 := by exact prefixLift 1195655
  have htrace : WordTrace (prefixWord ++ tailWord_1195655) baseStart_1195655 baseEnd_1195655 := by
    simpa [prefixWord, tailWord_1195655, baseEnd_1195655] using wordTrace_append hprefix tailTrace_1195655
  have hstable : (prefixWord ++ tailWord_1195655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195655).length < 2 ^ (prefixWord ++ tailWord_1195655).sum := by decide
  have hdescent : baseEnd_1195655 < baseStart_1195655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
