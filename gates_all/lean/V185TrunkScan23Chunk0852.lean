import V185TrunkScan23Chunk0851

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5042797 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 5]
def baseStart_5042797 : Nat := 118140960795 + 5042797 * 2 ^ 59
def prefixEnd_5042797 : Nat := 4983230072969 + 3 ^ 40 * 5042797 * 2
def baseEnd_5042797 : Nat := 287708744894556863027345

theorem tailTrace_5042797 : CollatzResearch.WordTrace tailWord_5042797 prefixEnd_5042797 287708744894556863027345 := by
  unfold tailWord_5042797
  simp only [CollatzResearch.WordTrace]
  refine ⟨183925916711815185005798645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122617277807876790003865763 183925916711815185005798645)
  ·
    refine ⟨17243054691732673594293623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183925916711815185005798645 17243054691732673594293623)
    ·
      refine ⟨25864582037599010391440435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17243054691732673594293623 25864582037599010391440435)
      ·
        refine ⟨38796873056398515587160653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25864582037599010391440435 38796873056398515587160653)
        ·
          refine ⟨14548827396149443345185245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38796873056398515587160653 14548827396149443345185245)
          ·
            refine ⟨5455810273556041254444467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14548827396149443345185245 5455810273556041254444467)
            ·
              refine ⟨8183715410334061881666701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455810273556041254444467 8183715410334061881666701)
              ·
                refine ⟨3068893278875273205625013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8183715410334061881666701 3068893278875273205625013)
                ·
                  refine ⟨287708744894556863027345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3068893278875273205625013 287708744894556863027345)
                  ·
                    rfl

theorem cell23_5042797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_5042797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042797 prefixEnd_5042797 := by exact prefixLift 5042797
  have htrace : WordTrace (prefixWord ++ tailWord_5042797) baseStart_5042797 baseEnd_5042797 := by
    simpa [prefixWord, tailWord_5042797, baseEnd_5042797] using wordTrace_append hprefix tailTrace_5042797
  have hstable : (prefixWord ++ tailWord_5042797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042797).length < 2 ^ (prefixWord ++ tailWord_5042797).sum := by decide
  have hdescent : baseEnd_5042797 < baseStart_5042797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042830 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5042830 : Nat := 118140960795 + 5042830 * 2 ^ 59
def prefixEnd_5042830 : Nat := 4983230072969 + 3 ^ 40 * 5042830 * 2
def baseEnd_5042830 : Nat := 2589395648912610138133453

theorem tailTrace_5042830 : CollatzResearch.WordTrace tailWord_5042830 prefixEnd_5042830 2589395648912610138133453 := by
  unfold tailWord_5042830
  simp only [CollatzResearch.WordTrace]
  refine ⟨22990890040086953955218743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122618080213797087761166629 22990890040086953955218743)
  ·
    refine ⟨34486335060130430932828115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22990890040086953955218743 34486335060130430932828115)
    ·
      refine ⟨51729502590195646399242173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34486335060130430932828115 51729502590195646399242173)
      ·
        refine ⟨19398563471323367399715815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51729502590195646399242173 19398563471323367399715815)
        ·
          refine ⟨29097845206985051099573723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19398563471323367399715815 29097845206985051099573723)
          ·
            refine ⟨43646767810477576649360585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29097845206985051099573723 43646767810477576649360585)
            ·
              refine ⟨32735075857858182487020439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43646767810477576649360585 32735075857858182487020439)
              ·
                refine ⟨49102613786787273730530659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32735075857858182487020439 49102613786787273730530659)
                ·
                  refine ⟨73653920680180910595795989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49102613786787273730530659 73653920680180910595795989)
                  ·
                    refine ⟨3452527531883480184177937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73653920680180910595795989 3452527531883480184177937)
                    ·
                      refine ⟨2589395648912610138133453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452527531883480184177937 2589395648912610138133453)
                      ·
                        rfl

theorem cell23_5042830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5042830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042830 prefixEnd_5042830 := by exact prefixLift 5042830
  have htrace : WordTrace (prefixWord ++ tailWord_5042830) baseStart_5042830 baseEnd_5042830 := by
    simpa [prefixWord, tailWord_5042830, baseEnd_5042830] using wordTrace_append hprefix tailTrace_5042830
  have hstable : (prefixWord ++ tailWord_5042830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042830).length < 2 ^ (prefixWord ++ tailWord_5042830).sum := by decide
  have hdescent : baseEnd_5042830 < baseStart_5042830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042901 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5042901 : Nat := 118140960795 + 5042901 * 2 ^ 59
def prefixEnd_5042901 : Nat := 4983230072969 + 3 ^ 40 * 5042901 * 2
def baseEnd_5042901 : Nat := 2589432106039079360345627

theorem tailTrace_5042901 : CollatzResearch.WordTrace tailWord_5042901 prefixEnd_5042901 2589432106039079360345627 := by
  unfold tailWord_5042901
  simp only [CollatzResearch.WordTrace]
  refine ⟨183929709903438410767584557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122619806602292273845056371 183929709903438410767584557)
  ·
    refine ⟨68973641213789404037844209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183929709903438410767584557 68973641213789404037844209)
    ·
      refine ⟨51730230910342053028383157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68973641213789404037844209 51730230910342053028383157)
      ·
        refine ⟨4849709147844567471410921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51730230910342053028383157 4849709147844567471410921)
        ·
          refine ⟨3637281860883425603558191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4849709147844567471410921 3637281860883425603558191)
          ·
            refine ⟨5455922791325138405337287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637281860883425603558191 5455922791325138405337287)
            ·
              refine ⟨8183884186987707608005931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455922791325138405337287 8183884186987707608005931)
              ·
                refine ⟨12275826280481561412008897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8183884186987707608005931 12275826280481561412008897)
                ·
                  refine ⟨9206869710361171059006673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12275826280481561412008897 9206869710361171059006673)
                  ·
                    refine ⟨6905152282770878294255005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9206869710361171059006673 6905152282770878294255005)
                    ·
                      refine ⟨2589432106039079360345627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6905152282770878294255005 2589432106039079360345627)
                      ·
                        rfl

theorem cell23_5042901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5042901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042901 prefixEnd_5042901 := by exact prefixLift 5042901
  have htrace : WordTrace (prefixWord ++ tailWord_5042901) baseStart_5042901 baseEnd_5042901 := by
    simpa [prefixWord, tailWord_5042901, baseEnd_5042901] using wordTrace_append hprefix tailTrace_5042901
  have hstable : (prefixWord ++ tailWord_5042901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042901).length < 2 ^ (prefixWord ++ tailWord_5042901).sum := by decide
  have hdescent : baseEnd_5042901 < baseStart_5042901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042917 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_5042917 : Nat := 118140960795 + 5042917 * 2 ^ 59
def prefixEnd_5042917 : Nat := 4983230072969 + 3 ^ 40 * 5042917 * 2
def baseEnd_5042917 : Nat := 863146773909850432581851

theorem tailTrace_5042917 : CollatzResearch.WordTrace tailWord_5042917 prefixEnd_5042917 863146773909850432581851 := by
  unfold tailWord_5042917
  simp only [CollatzResearch.WordTrace]
  refine ⟨183930293471380445500167005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122620195647586963666778003 183930293471380445500167005)
  ·
    refine ⟨68973860051767667062562627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183930293471380445500167005 68973860051767667062562627)
    ·
      refine ⟨103460790077651500593843941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68973860051767667062562627 103460790077651500593843941)
      ·
        refine ⟨19398898139559656361345739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103460790077651500593843941 19398898139559656361345739)
        ·
          refine ⟨29098347209339484542018609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19398898139559656361345739 29098347209339484542018609)
          ·
            refine ⟨21823760407004613406513957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29098347209339484542018609 21823760407004613406513957)
            ·
              refine ⟨4091955076313365013721367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21823760407004613406513957 4091955076313365013721367)
              ·
                refine ⟨6137932614470047520582051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091955076313365013721367 6137932614470047520582051)
                ·
                  refine ⟨9206898921705071280873077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137932614470047520582051 9206898921705071280873077)
                  ·
                    refine ⟨863146773909850432581851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9206898921705071280873077 863146773909850432581851)
                    ·
                      rfl

theorem cell23_5042917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_5042917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042917 prefixEnd_5042917 := by exact prefixLift 5042917
  have htrace : WordTrace (prefixWord ++ tailWord_5042917) baseStart_5042917 baseEnd_5042917 := by
    simpa [prefixWord, tailWord_5042917, baseEnd_5042917] using wordTrace_append hprefix tailTrace_5042917
  have hstable : (prefixWord ++ tailWord_5042917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042917).length < 2 ^ (prefixWord ++ tailWord_5042917).sum := by decide
  have hdescent : baseEnd_5042917 < baseStart_5042917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042923 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5]
def baseStart_5042923 : Nat := 118140960795 + 5042923 * 2 ^ 59
def prefixEnd_5042923 : Nat := 4983230072969 + 3 ^ 40 * 5042923 * 2
def baseEnd_5042923 : Nat := 2589443402613478274270525

theorem tailTrace_5042923 : CollatzResearch.WordTrace tailWord_5042923 prefixEnd_5042923 2589443402613478274270525 := by
  unfold tailWord_5042923
  simp only [CollatzResearch.WordTrace]
  refine ⟨183930512309358708524885423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122620341539572472349923615 183930512309358708524885423)
  ·
    refine ⟨275895768464038062787328135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183930512309358708524885423 275895768464038062787328135)
    ·
      refine ⟨413843652696057094180992203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275895768464038062787328135 413843652696057094180992203)
      ·
        refine ⟨620765479044085641271488305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413843652696057094180992203 620765479044085641271488305)
        ·
          refine ⟨465574109283064230953616229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620765479044085641271488305 465574109283064230953616229)
          ·
            refine ⟨87295145490574543303803043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 465574109283064230953616229 87295145490574543303803043)
            ·
              refine ⟨130942718235861814955704565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87295145490574543303803043 130942718235861814955704565)
              ·
                refine ⟨12275879834612045152097303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130942718235861814955704565 12275879834612045152097303)
                ·
                  refine ⟨18413819751918067728145955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12275879834612045152097303 18413819751918067728145955)
                  ·
                    refine ⟨27620729627877101592218933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18413819751918067728145955 27620729627877101592218933)
                    ·
                      refine ⟨2589443402613478274270525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27620729627877101592218933 2589443402613478274270525)
                      ·
                        rfl

theorem cell23_5042923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_5042923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042923 prefixEnd_5042923 := by exact prefixLift 5042923
  have htrace : WordTrace (prefixWord ++ tailWord_5042923) baseStart_5042923 baseEnd_5042923 := by
    simpa [prefixWord, tailWord_5042923, baseEnd_5042923] using wordTrace_append hprefix tailTrace_5042923
  have hstable : (prefixWord ++ tailWord_5042923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042923).length < 2 ^ (prefixWord ++ tailWord_5042923).sum := by decide
  have hdescent : baseEnd_5042923 < baseStart_5042923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042940 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_5042940 : Nat := 118140960795 + 5042940 * 2 ^ 59
def prefixEnd_5042940 : Nat := 4983230072969 + 3 ^ 40 * 5042940 * 2
def baseEnd_5042940 : Nat := 2589452131784604707757947

theorem tailTrace_5042940 : CollatzResearch.WordTrace tailWord_5042940 prefixEnd_5042940 2589452131784604707757947 := by
  unfold tailWord_5042940
  simp only [CollatzResearch.WordTrace]
  refine ⟨91965566175148560214127137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122620754900198080285502849 91965566175148560214127137)
  ·
    refine ⟨68974174631361420160595353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91965566175148560214127137 68974174631361420160595353)
    ·
      refine ⟨51730630973521065120446515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68974174631361420160595353 51730630973521065120446515)
      ·
        refine ⟨77595946460281597680669773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51730630973521065120446515 77595946460281597680669773)
        ·
          refine ⟨29098479922605599130251165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77595946460281597680669773 29098479922605599130251165)
          ·
            refine ⟨10911929970977099673844187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29098479922605599130251165 10911929970977099673844187)
            ·
              refine ⟨16367894956465649510766281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10911929970977099673844187 16367894956465649510766281)
              ·
                refine ⟨12275921217349237133074711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16367894956465649510766281 12275921217349237133074711)
                ·
                  refine ⟨18413881826023855699612067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12275921217349237133074711 18413881826023855699612067)
                  ·
                    refine ⟨27620822739035783549418101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18413881826023855699612067 27620822739035783549418101)
                    ·
                      refine ⟨2589452131784604707757947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27620822739035783549418101 2589452131784604707757947)
                      ·
                        rfl

theorem cell23_5042940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_5042940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042940 prefixEnd_5042940 := by exact prefixLift 5042940
  have htrace : WordTrace (prefixWord ++ tailWord_5042940) baseStart_5042940 baseEnd_5042940 := by
    simpa [prefixWord, tailWord_5042940, baseEnd_5042940] using wordTrace_append hprefix tailTrace_5042940
  have hstable : (prefixWord ++ tailWord_5042940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042940).length < 2 ^ (prefixWord ++ tailWord_5042940).sum := by decide
  have hdescent : baseEnd_5042940 < baseStart_5042940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042970 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_5042970 : Nat := 118140960795 + 5042970 * 2 ^ 59
def prefixEnd_5042970 : Nat := 4983230072969 + 3 ^ 40 * 5042970 * 2
def baseEnd_5042970 : Nat := 2589467536204239590382809

theorem tailTrace_5042970 : CollatzResearch.WordTrace tailWord_5042970 prefixEnd_5042970 2589467536204239590382809 := by
  unfold tailWord_5042970
  simp only [CollatzResearch.WordTrace]
  refine ⟨45983056635047108887961591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122621484360125623701230909 45983056635047108887961591)
  ·
    refine ⟨68974584952570663331942387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45983056635047108887961591 68974584952570663331942387)
    ·
      refine ⟨103461877428855994997913581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68974584952570663331942387 103461877428855994997913581)
      ·
        refine ⟨38798204035820998124217593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103461877428855994997913581 38798204035820998124217593)
        ·
          refine ⟨29098653026865748593163195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38798204035820998124217593 29098653026865748593163195)
          ·
            refine ⟨43647979540298622889744793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29098653026865748593163195 43647979540298622889744793)
            ·
              refine ⟨32735984655223967167308595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43647979540298622889744793 32735984655223967167308595)
              ·
                refine ⟨49103976982835950750962893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32735984655223967167308595 49103976982835950750962893)
                ·
                  refine ⟨18413991368563481531611085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49103976982835950750962893 18413991368563481531611085)
                  ·
                    refine ⟨6905246763211305574354157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18413991368563481531611085 6905246763211305574354157)
                    ·
                      refine ⟨2589467536204239590382809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6905246763211305574354157 2589467536204239590382809)
                      ·
                        rfl

theorem cell23_5042970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_5042970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042970 prefixEnd_5042970 := by exact prefixLift 5042970
  have htrace : WordTrace (prefixWord ++ tailWord_5042970) baseStart_5042970 baseEnd_5042970 := by
    simpa [prefixWord, tailWord_5042970, baseEnd_5042970] using wordTrace_append hprefix tailTrace_5042970
  have hstable : (prefixWord ++ tailWord_5042970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042970).length < 2 ^ (prefixWord ++ tailWord_5042970).sum := by decide
  have hdescent : baseEnd_5042970 < baseStart_5042970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5042998 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5042998 : Nat := 118140960795 + 5042998 * 2 ^ 59
def prefixEnd_5042998 : Nat := 4983230072969 + 3 ^ 40 * 5042998 * 2
def baseEnd_5042998 : Nat := 863160637887521826944227

theorem tailTrace_5042998 : CollatzResearch.WordTrace tailWord_5042998 prefixEnd_5042998 863160637887521826944227 := by
  unfold tailWord_5042998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495827986505437270866603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122622165189391330889243765 11495827986505437270866603)
  ·
    refine ⟨17243741979758155906299905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11495827986505437270866603 17243741979758155906299905)
    ·
      refine ⟨12932806484818616929724929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17243741979758155906299905 12932806484818616929724929)
      ·
        refine ⟨9699604863613962697293697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12932806484818616929724929 9699604863613962697293697)
        ·
          refine ⟨7274703647710472022970273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9699604863613962697293697 7274703647710472022970273)
          ·
            refine ⟨5456027735782854017227705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7274703647710472022970273 5456027735782854017227705)
            ·
              refine ⟨4092020801837140512920779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5456027735782854017227705 4092020801837140512920779)
              ·
                refine ⟨6138031202755710769381169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092020801837140512920779 6138031202755710769381169)
                ·
                  refine ⟨4603523402066783077035877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138031202755710769381169 4603523402066783077035877)
                  ·
                    refine ⟨863160637887521826944227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603523402066783077035877 863160637887521826944227)
                    ·
                      rfl

theorem cell23_5042998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5042998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5042998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5042998 prefixEnd_5042998 := by exact prefixLift 5042998
  have htrace : WordTrace (prefixWord ++ tailWord_5042998) baseStart_5042998 baseEnd_5042998 := by
    simpa [prefixWord, tailWord_5042998, baseEnd_5042998] using wordTrace_append hprefix tailTrace_5042998
  have hstable : (prefixWord ++ tailWord_5042998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5042998).length < 2 ^ (prefixWord ++ tailWord_5042998).sum := by decide
  have hdescent : baseEnd_5042998 < baseStart_5042998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5042998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043027 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 6, 2, 2]
def baseStart_5043027 : Nat := 118140960795 + 5043027 * 2 ^ 59
def prefixEnd_5043027 : Nat := 4983230072969 + 3 ^ 40 * 5043027 * 2
def baseEnd_5043027 : Nat := 2589496804601545867370047

theorem tailTrace_5043027 : CollatzResearch.WordTrace tailWord_5043027 prefixEnd_5043027 2589496804601545867370047 := by
  unfold tailWord_5043027
  simp only [CollatzResearch.WordTrace]
  refine ⟨183934305500981934286671335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122622870333987956191114223 183934305500981934286671335)
  ·
    refine ⟨275901458251472901430007003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183934305500981934286671335 275901458251472901430007003)
    ·
      refine ⟨413852187377209352145010505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275901458251472901430007003 413852187377209352145010505)
      ·
        refine ⟨310389140532907014108757879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413852187377209352145010505 310389140532907014108757879)
        ·
          refine ⟨465583710799360521163136819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310389140532907014108757879 465583710799360521163136819)
          ·
            refine ⟨698375566199040781744705229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465583710799360521163136819 698375566199040781744705229)
            ·
              refine ⟨261890837324640293154264461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698375566199040781744705229 261890837324640293154264461)
              ·
                refine ⟨98209063996740109932849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261890837324640293154264461 98209063996740109932849173)
                ·
                  refine ⟨4603549874847192653102305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98209063996740109932849173 4603549874847192653102305)
                  ·
                    refine ⟨3452662406135394489826729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603549874847192653102305 3452662406135394489826729)
                    ·
                      refine ⟨2589496804601545867370047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452662406135394489826729 2589496804601545867370047)
                      ·
                        rfl

theorem cell23_5043027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2, 2].length) (baseStart_5043027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043027 prefixEnd_5043027 := by exact prefixLift 5043027
  have htrace : WordTrace (prefixWord ++ tailWord_5043027) baseStart_5043027 baseEnd_5043027 := by
    simpa [prefixWord, tailWord_5043027, baseEnd_5043027] using wordTrace_append hprefix tailTrace_5043027
  have hstable : (prefixWord ++ tailWord_5043027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043027).length < 2 ^ (prefixWord ++ tailWord_5043027).sum := by decide
  have hdescent : baseEnd_5043027 < baseStart_5043027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043031 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_5043031 : Nat := 118140960795 + 5043031 * 2 ^ 59
def prefixEnd_5043031 : Nat := 4983230072969 + 3 ^ 40 * 5043031 * 2
def baseEnd_5043031 : Nat := 2589498858524163851720029

theorem tailTrace_5043031 : CollatzResearch.WordTrace tailWord_5043031 prefixEnd_5043031 2589498858524163851720029 := by
  unfold tailWord_5043031
  simp only [CollatzResearch.WordTrace]
  refine ⟨183934451392967442969816947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122622967595311628646544631 183934451392967442969816947)
  ·
    refine ⟨275901677089451164454725421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183934451392967442969816947 275901677089451164454725421)
    ·
      refine ⟨103463128908544186670522033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275901677089451164454725421 103463128908544186670522033)
      ·
        refine ⟨77597346681408140002891525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103463128908544186670522033 77597346681408140002891525)
        ·
          refine ⟨14549502502764026250542161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77597346681408140002891525 14549502502764026250542161)
          ·
            refine ⟨10912126877073019687906621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14549502502764026250542161 10912126877073019687906621)
            ·
              refine ⟨4092047578902382382964983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10912126877073019687906621 4092047578902382382964983)
              ·
                refine ⟨6138071368353573574447475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092047578902382382964983 6138071368353573574447475)
                ·
                  refine ⟨9207107052530360361671213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138071368353573574447475 9207107052530360361671213)
                  ·
                    refine ⟨3452665144698885135626705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9207107052530360361671213 3452665144698885135626705)
                    ·
                      refine ⟨2589498858524163851720029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452665144698885135626705 2589498858524163851720029)
                      ·
                        rfl

theorem cell23_5043031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_5043031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043031 prefixEnd_5043031 := by exact prefixLift 5043031
  have htrace : WordTrace (prefixWord ++ tailWord_5043031) baseStart_5043031 baseEnd_5043031 := by
    simpa [prefixWord, tailWord_5043031, baseEnd_5043031] using wordTrace_append hprefix tailTrace_5043031
  have hstable : (prefixWord ++ tailWord_5043031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043031).length < 2 ^ (prefixWord ++ tailWord_5043031).sum := by decide
  have hdescent : baseEnd_5043031 < baseStart_5043031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043040 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_5043040 : Nat := 118140960795 + 5043040 * 2 ^ 59
def prefixEnd_5043040 : Nat := 4983230072969 + 3 ^ 40 * 5043040 * 2
def baseEnd_5043040 : Nat := 2589503479850054316507487

theorem tailTrace_5043040 : CollatzResearch.WordTrace tailWord_5043040 prefixEnd_5043040 2589503479850054316507487 := by
  unfold tailWord_5043040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91967389824967418753447287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122623186433289891671263049 91967389824967418753447287)
  ·
    refine ⟨137951084737451128130170931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91967389824967418753447287 137951084737451128130170931)
    ·
      refine ⟨206926627106176692195256397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137951084737451128130170931 206926627106176692195256397)
      ·
        refine ⟨77597485164816259573221149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206926627106176692195256397 77597485164816259573221149)
        ·
          refine ⟨29099056936806097339957931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77597485164816259573221149 29099056936806097339957931)
          ·
            refine ⟨43648585405209146009936897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29099056936806097339957931 43648585405209146009936897)
            ·
              refine ⟨32736439053906859507452673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43648585405209146009936897 32736439053906859507452673)
              ·
                refine ⟨24552329290430144630589505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32736439053906859507452673 24552329290430144630589505)
                ·
                  refine ⟨18414246967822608472942129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24552329290430144630589505 18414246967822608472942129)
                  ·
                    refine ⟨13810685225866956354706597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18414246967822608472942129 13810685225866956354706597)
                    ·
                      refine ⟨2589503479850054316507487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13810685225866956354706597 2589503479850054316507487)
                      ·
                        rfl

theorem cell23_5043040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_5043040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043040 prefixEnd_5043040 := by exact prefixLift 5043040
  have htrace : WordTrace (prefixWord ++ tailWord_5043040) baseStart_5043040 baseEnd_5043040 := by
    simpa [prefixWord, tailWord_5043040, baseEnd_5043040] using wordTrace_append hprefix tailTrace_5043040
  have hstable : (prefixWord ++ tailWord_5043040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043040).length < 2 ^ (prefixWord ++ tailWord_5043040).sum := by decide
  have hdescent : baseEnd_5043040 < baseStart_5043040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043061 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_5043061 : Nat := 118140960795 + 5043061 * 2 ^ 59
def prefixEnd_5043061 : Nat := 4983230072969 + 3 ^ 40 * 5043061 * 2
def baseEnd_5043061 : Nat := 2589514262943798734344891

theorem tailTrace_5043061 : CollatzResearch.WordTrace tailWord_5043061 prefixEnd_5043061 2589514262943798734344891 := by
  unfold tailWord_5043061
  simp only [CollatzResearch.WordTrace]
  refine ⟨183935545582858758093409037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122623697055239172062272691 183935545582858758093409037)
  ·
    refine ⟨68975829593572034285028389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183935545582858758093409037 68975829593572034285028389)
    ·
      refine ⟨12932968048794756428442823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68975829593572034285028389 12932968048794756428442823)
      ·
        refine ⟨19399452073192134642664235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12932968048794756428442823 19399452073192134642664235)
        ·
          refine ⟨29099178109788201963996353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19399452073192134642664235 29099178109788201963996353)
          ·
            refine ⟨21824383582341151472997265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29099178109788201963996353 21824383582341151472997265)
            ·
              refine ⟨16368287686755863604747949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21824383582341151472997265 16368287686755863604747949)
              ·
                refine ⟨6138107882533448851780481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16368287686755863604747949 6138107882533448851780481)
                ·
                  refine ⟨4603580911900086638835361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138107882533448851780481 4603580911900086638835361)
                  ·
                    refine ⟨3452685683925064979126521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603580911900086638835361 3452685683925064979126521)
                    ·
                      refine ⟨2589514262943798734344891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452685683925064979126521 2589514262943798734344891)
                      ·
                        rfl

theorem cell23_5043061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_5043061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043061 prefixEnd_5043061 := by exact prefixLift 5043061
  have htrace : WordTrace (prefixWord ++ tailWord_5043061) baseStart_5043061 baseEnd_5043061 := by
    simpa [prefixWord, tailWord_5043061, baseEnd_5043061] using wordTrace_append hprefix tailTrace_5043061
  have hstable : (prefixWord ++ tailWord_5043061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043061).length < 2 ^ (prefixWord ++ tailWord_5043061).sum := by decide
  have hdescent : baseEnd_5043061 < baseStart_5043061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043127 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 3, 4]
def baseStart_5043127 : Nat := 118140960795 + 5043127 * 2 ^ 59
def prefixEnd_5043127 : Nat := 4983230072969 + 3 ^ 40 * 5043127 * 2
def baseEnd_5043127 : Nat := 863182717555665158706529

theorem tailTrace_5043127 : CollatzResearch.WordTrace tailWord_5043127 prefixEnd_5043127 863182717555665158706529 := by
  unfold tailWord_5043127
  simp only [CollatzResearch.WordTrace]
  refine ⟨183937952800619651365311635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122625301867079767576874423 183937952800619651365311635)
  ·
    refine ⟨275906929200929477047967453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183937952800619651365311635 275906929200929477047967453)
    ·
      refine ⟨103465098450348553892987795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275906929200929477047967453 103465098450348553892987795)
      ·
        refine ⟨155197647675522830839481693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103465098450348553892987795 155197647675522830839481693)
        ·
          refine ⟨58199117878321061564805635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155197647675522830839481693 58199117878321061564805635)
          ·
            refine ⟨87298676817481592347208453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58199117878321061564805635 87298676817481592347208453)
            ·
              refine ⟨16368501903277798565101585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87298676817481592347208453 16368501903277798565101585)
              ·
                refine ⟨12276376427458348923826189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16368501903277798565101585 12276376427458348923826189)
                ·
                  refine ⟨4603641160296880846434821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12276376427458348923826189 4603641160296880846434821)
                  ·
                    refine ⟨863182717555665158706529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603641160296880846434821 863182717555665158706529)
                    ·
                      rfl

theorem cell23_5043127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_5043127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043127 prefixEnd_5043127 := by exact prefixLift 5043127
  have htrace : WordTrace (prefixWord ++ tailWord_5043127) baseStart_5043127 baseEnd_5043127 := by
    simpa [prefixWord, tailWord_5043127, baseEnd_5043127] using wordTrace_append hprefix tailTrace_5043127
  have hstable : (prefixWord ++ tailWord_5043127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043127).length < 2 ^ (prefixWord ++ tailWord_5043127).sum := by decide
  have hdescent : baseEnd_5043127 < baseStart_5043127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043130 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_5043130 : Nat := 118140960795 + 5043130 * 2 ^ 59
def prefixEnd_5043130 : Nat := 4983230072969 + 3 ^ 40 * 5043130 * 2
def baseEnd_5043130 : Nat := 2589549693108958964382073

theorem tailTrace_5043130 : CollatzResearch.WordTrace tailWord_5043130 prefixEnd_5043130 2589549693108958964382073 := by
  unfold tailWord_5043130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45984515554902195719417711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122625374813072521918447229 45984515554902195719417711)
  ·
    refine ⟨68976773332353293579126567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45984515554902195719417711 68976773332353293579126567)
    ·
      refine ⟨103465159998529940368689851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68976773332353293579126567 103465159998529940368689851)
      ·
        refine ⟨155197739997794910553034777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103465159998529940368689851 155197739997794910553034777)
        ·
          refine ⟨116398304998346182914776083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155197739997794910553034777 116398304998346182914776083)
          ·
            refine ⟨174597457497519274372164125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116398304998346182914776083 174597457497519274372164125)
            ·
              refine ⟨65474046561569727889561547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174597457497519274372164125 65474046561569727889561547)
              ·
                refine ⟨98211069842354591834342321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65474046561569727889561547 98211069842354591834342321)
                ·
                  refine ⟨73658302381765943875756741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98211069842354591834342321 73658302381765943875756741)
                  ·
                    refine ⟨13810931696581114476704389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73658302381765943875756741 13810931696581114476704389)
                    ·
                      refine ⟨2589549693108958964382073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13810931696581114476704389 2589549693108958964382073)
                      ·
                        rfl

theorem cell23_5043130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_5043130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043130 prefixEnd_5043130 := by exact prefixLift 5043130
  have htrace : WordTrace (prefixWord ++ tailWord_5043130) baseStart_5043130 baseEnd_5043130 := by
    simpa [prefixWord, tailWord_5043130, baseEnd_5043130] using wordTrace_append hprefix tailTrace_5043130
  have hstable : (prefixWord ++ tailWord_5043130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043130).length < 2 ^ (prefixWord ++ tailWord_5043130).sum := by decide
  have hdescent : baseEnd_5043130 < baseStart_5043130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043154 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5043154 : Nat := 118140960795 + 5043154 * 2 ^ 59
def prefixEnd_5043154 : Nat := 4983230072969 + 3 ^ 40 * 5043154 * 2
def baseEnd_5043154 : Nat := 2589562016644666870481963

theorem tailTrace_5043154 : CollatzResearch.WordTrace tailWord_5043154 prefixEnd_5043154 2589562016644666870481963 := by
  unfold tailWord_5043154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45984734392880458744136129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122625958381014556651029677 45984734392880458744136129)
  ·
    refine ⟨34488550794660344058102097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45984734392880458744136129 34488550794660344058102097)
    ·
      refine ⟨25866413095995258043576573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34488550794660344058102097 25866413095995258043576573)
      ·
        refine ⟨9699904910998221766341215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25866413095995258043576573 9699904910998221766341215)
        ·
          refine ⟨14549857366497332649511823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699904910998221766341215 14549857366497332649511823)
          ·
            refine ⟨21824786049745998974267735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14549857366497332649511823 21824786049745998974267735)
            ·
              refine ⟨32737179074618998461401603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21824786049745998974267735 32737179074618998461401603)
              ·
                refine ⟨49105768611928497692102405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32737179074618998461401603 49105768611928497692102405)
                ·
                  refine ⟨9207331614736593317269201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49105768611928497692102405 9207331614736593317269201)
                  ·
                    refine ⟨6905498711052444987951901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9207331614736593317269201 6905498711052444987951901)
                    ·
                      refine ⟨2589562016644666870481963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6905498711052444987951901 2589562016644666870481963)
                      ·
                        rfl

theorem cell23_5043154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5043154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043154 prefixEnd_5043154 := by exact prefixLift 5043154
  have htrace : WordTrace (prefixWord ++ tailWord_5043154) baseStart_5043154 baseEnd_5043154 := by
    simpa [prefixWord, tailWord_5043154, baseEnd_5043154] using wordTrace_append hprefix tailTrace_5043154
  have hstable : (prefixWord ++ tailWord_5043154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043154).length < 2 ^ (prefixWord ++ tailWord_5043154).sum := by decide
  have hdescent : baseEnd_5043154 < baseStart_5043154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043217 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_5043217 : Nat := 118140960795 + 5043217 * 2 ^ 59
def prefixEnd_5043217 : Nat := 4983230072969 + 3 ^ 40 * 5043217 * 2
def baseEnd_5043217 : Nat := 863198121975300041331391

theorem tailTrace_5043217 : CollatzResearch.WordTrace tailWord_5043217 prefixEnd_5043217 863198121975300041331391 := by
  unfold tailWord_5043217
  simp only [CollatzResearch.WordTrace]
  refine ⟨183941235370293596736087905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122627490246862397824058603 183941235370293596736087905)
  ·
    refine ⟨137955926527720197552065929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183941235370293596736087905 137955926527720197552065929)
    ·
      refine ⟨103466944895790148164049447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137955926527720197552065929 103466944895790148164049447)
      ·
        refine ⟨155200417343685222246074171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103466944895790148164049447 155200417343685222246074171)
        ·
          refine ⟨232800626015527833369111257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155200417343685222246074171 232800626015527833369111257)
          ·
            refine ⟨174600469511645875026833443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232800626015527833369111257 174600469511645875026833443)
            ·
              refine ⟨261900704267468812540250165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174600469511645875026833443 261900704267468812540250165)
              ·
                refine ⟨24553191025075201175648453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261900704267468812540250165 24553191025075201175648453)
                ·
                  refine ⟨4603723317201600220434085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24553191025075201175648453 4603723317201600220434085)
                  ·
                    refine ⟨863198121975300041331391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603723317201600220434085 863198121975300041331391)
                    ·
                      rfl

theorem cell23_5043217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_5043217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043217 prefixEnd_5043217 := by exact prefixLift 5043217
  have htrace : WordTrace (prefixWord ++ tailWord_5043217) baseStart_5043217 baseEnd_5043217 := by
    simpa [prefixWord, tailWord_5043217, baseEnd_5043217] using wordTrace_append hprefix tailTrace_5043217
  have hstable : (prefixWord ++ tailWord_5043217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043217).length < 2 ^ (prefixWord ++ tailWord_5043217).sum := by decide
  have hdescent : baseEnd_5043217 < baseStart_5043217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043234 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5043234 : Nat := 118140960795 + 5043234 * 2 ^ 59
def prefixEnd_5043234 : Nat := 4983230072969 + 3 ^ 40 * 5043234 * 2
def baseEnd_5043234 : Nat := 863201031699008852493865

theorem tailTrace_5043234 : CollatzResearch.WordTrace tailWord_5043234 prefixEnd_5043234 863201031699008852493865 := by
  unfold tailWord_5043234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45985463852808002159864189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122627903607488005759637837 45985463852808002159864189)
  ·
    refine ⟨17244548944803000809949071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45985463852808002159864189 17244548944803000809949071)
    ·
      refine ⟨25866823417204501214923607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17244548944803000809949071 25866823417204501214923607)
      ·
        refine ⟨38800235125806751822385411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25866823417204501214923607 38800235125806751822385411)
        ·
          refine ⟨58200352688710127733578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38800235125806751822385411 58200352688710127733578117)
          ·
            refine ⟨10912566129133148950045897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58200352688710127733578117 10912566129133148950045897)
            ·
              refine ⟨8184424596849861712534423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10912566129133148950045897 8184424596849861712534423)
              ·
                refine ⟨12276636895274792568801635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8184424596849861712534423 12276636895274792568801635)
                ·
                  refine ⟨18414955342912188853202453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12276636895274792568801635 18414955342912188853202453)
                  ·
                    refine ⟨863201031699008852493865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18414955342912188853202453 863201031699008852493865)
                    ·
                      rfl

theorem cell23_5043234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5043234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043234 prefixEnd_5043234 := by exact prefixLift 5043234
  have htrace : WordTrace (prefixWord ++ tailWord_5043234) baseStart_5043234 baseEnd_5043234 := by
    simpa [prefixWord, tailWord_5043234, baseEnd_5043234] using wordTrace_append hprefix tailTrace_5043234
  have hstable : (prefixWord ++ tailWord_5043234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043234).length < 2 ^ (prefixWord ++ tailWord_5043234).sum := by decide
  have hdescent : baseEnd_5043234 < baseStart_5043234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043244 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_5043244 : Nat := 118140960795 + 5043244 * 2 ^ 59
def prefixEnd_5043244 : Nat := 4983230072969 + 3 ^ 40 * 5043244 * 2
def baseEnd_5043244 : Nat := 2589608229903571518356549

theorem tailTrace_5043244 : CollatzResearch.WordTrace tailWord_5043244 prefixEnd_5043244 2589608229903571518356549 := by
  unfold tailWord_5043244
  simp only [CollatzResearch.WordTrace]
  refine ⟨91971110070597890173660393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122628146760797186898213857 91971110070597890173660393)
  ·
    refine ⟨68978332552948417630245295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91971110070597890173660393 68978332552948417630245295)
    ·
      refine ⟨103467498829422626445367943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68978332552948417630245295 103467498829422626445367943)
      ·
        refine ⟨155201248244133939668051915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103467498829422626445367943 155201248244133939668051915)
        ·
          refine ⟨232801872366200909502077873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155201248244133939668051915 232801872366200909502077873)
          ·
            refine ⟨174601404274650682126558405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232801872366200909502077873 174601404274650682126558405)
            ·
              refine ⟨32737763301497002898729701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174601404274650682126558405 32737763301497002898729701)
              ·
                refine ⟨6138330619030688043511819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32737763301497002898729701 6138330619030688043511819)
                ·
                  refine ⟨9207495928546032065267729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138330619030688043511819 9207495928546032065267729)
                  ·
                    refine ⟨6905621946409524048950797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9207495928546032065267729 6905621946409524048950797)
                    ·
                      refine ⟨2589608229903571518356549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6905621946409524048950797 2589608229903571518356549)
                      ·
                        rfl

theorem cell23_5043244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_5043244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043244 prefixEnd_5043244 := by exact prefixLift 5043244
  have htrace : WordTrace (prefixWord ++ tailWord_5043244) baseStart_5043244 baseEnd_5043244 := by
    simpa [prefixWord, tailWord_5043244, baseEnd_5043244] using wordTrace_append hprefix tailTrace_5043244
  have hstable : (prefixWord ++ tailWord_5043244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043244).length < 2 ^ (prefixWord ++ tailWord_5043244).sum := by decide
  have hdescent : baseEnd_5043244 < baseStart_5043244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043258 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2]
def baseStart_5043258 : Nat := 118140960795 + 5043258 * 2 ^ 59
def prefixEnd_5043258 : Nat := 4983230072969 + 3 ^ 40 * 5043258 * 2
def baseEnd_5043258 : Nat := 2589615418632734463581485

theorem tailTrace_5043258 : CollatzResearch.WordTrace tailWord_5043258 prefixEnd_5043258 2589615418632734463581485 := by
  unfold tailWord_5043258
  simp only [CollatzResearch.WordTrace]
  refine ⟨45985682690786265184582607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122628487175430040492220285 45985682690786265184582607)
  ·
    refine ⟨68978524036179397776873911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45985682690786265184582607 68978524036179397776873911)
    ·
      refine ⟨103467786054269096665310867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68978524036179397776873911 103467786054269096665310867)
      ·
        refine ⟨155201679081403644997966301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103467786054269096665310867 155201679081403644997966301)
        ·
          refine ⟨58200629655526366874237363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155201679081403644997966301 58200629655526366874237363)
          ·
            refine ⟨87300944483289550311356045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58200629655526366874237363 87300944483289550311356045)
            ·
              refine ⟨32737854181233581366758517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87300944483289550311356045 32737854181233581366758517)
              ·
                refine ⟨3069173829490648253133611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32737854181233581366758517 3069173829490648253133611)
                ·
                  refine ⟨4603760744235972379700417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069173829490648253133611 4603760744235972379700417)
                  ·
                    refine ⟨3452820558176979284775313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603760744235972379700417 3452820558176979284775313)
                    ·
                      refine ⟨2589615418632734463581485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452820558176979284775313 2589615418632734463581485)
                      ·
                        rfl

theorem cell23_5043258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_5043258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043258 prefixEnd_5043258 := by exact prefixLift 5043258
  have htrace : WordTrace (prefixWord ++ tailWord_5043258) baseStart_5043258 baseEnd_5043258 := by
    simpa [prefixWord, tailWord_5043258, baseEnd_5043258] using wordTrace_append hprefix tailTrace_5043258
  have hstable : (prefixWord ++ tailWord_5043258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043258).length < 2 ^ (prefixWord ++ tailWord_5043258).sum := by decide
  have hdescent : baseEnd_5043258 < baseStart_5043258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043261 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5043261 : Nat := 118140960795 + 5043261 * 2 ^ 59
def prefixEnd_5043261 : Nat := 4983230072969 + 3 ^ 40 * 5043261 * 2
def baseEnd_5043261 : Nat := 2589616959074697951843971

theorem tailTrace_5043261 : CollatzResearch.WordTrace tailWord_5043261 prefixEnd_5043261 2589616959074697951843971 := by
  unfold tailWord_5043261
  simp only [CollatzResearch.WordTrace]
  refine ⟨183942840182134192250689637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122628560121422794833793091 183942840182134192250689637)
  ·
    refine ⟨34489282534150161047004307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183942840182134192250689637 34489282534150161047004307)
    ·
      refine ⟨51733923801225241570506461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34489282534150161047004307 51733923801225241570506461)
      ·
        refine ⟨19400221425459465588939923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51733923801225241570506461 19400221425459465588939923)
        ·
          refine ⟨29100332138189198383409885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19400221425459465588939923 29100332138189198383409885)
          ·
            refine ⟨10912624551820949393778707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29100332138189198383409885 10912624551820949393778707)
            ·
              refine ⟨16368936827731424090668061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10912624551820949393778707 16368936827731424090668061)
              ·
                refine ⟨6138351310399284034000523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16368936827731424090668061 6138351310399284034000523)
                ·
                  refine ⟨9207526965598926051000785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138351310399284034000523 9207526965598926051000785)
                  ·
                    refine ⟨6905645224199194538250589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9207526965598926051000785 6905645224199194538250589)
                    ·
                      refine ⟨2589616959074697951843971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6905645224199194538250589 2589616959074697951843971)
                      ·
                        rfl

theorem cell23_5043261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5043261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043261 prefixEnd_5043261 := by exact prefixLift 5043261
  have htrace : WordTrace (prefixWord ++ tailWord_5043261) baseStart_5043261 baseEnd_5043261 := by
    simpa [prefixWord, tailWord_5043261, baseEnd_5043261] using wordTrace_append hprefix tailTrace_5043261
  have hstable : (prefixWord ++ tailWord_5043261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043261).length < 2 ^ (prefixWord ++ tailWord_5043261).sum := by decide
  have hdescent : baseEnd_5043261 < baseStart_5043261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043297 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_5043297 : Nat := 118140960795 + 5043297 * 2 ^ 59
def prefixEnd_5043297 : Nat := 4983230072969 + 3 ^ 40 * 5043297 * 2
def baseEnd_5043297 : Nat := 2589635444378259810993805

theorem tailTrace_5043297 : CollatzResearch.WordTrace tailWord_5043297 prefixEnd_5043297 2589635444378259810993805 := by
  unfold tailWord_5043297
  simp only [CollatzResearch.WordTrace]
  refine ⟨183944153210003770399000145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122629435473335846932666763 183944153210003770399000145)
  ·
    refine ⟨137958114907502827799250109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183944153210003770399000145 137958114907502827799250109)
    ·
      refine ⟨51734293090313560424718791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137958114907502827799250109 51734293090313560424718791)
      ·
        refine ⟨77601439635470340637078187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51734293090313560424718791 77601439635470340637078187)
        ·
          refine ⟨116402159453205510955617281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77601439635470340637078187 116402159453205510955617281)
          ·
            refine ⟨87301619589904133216712961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116402159453205510955617281 87301619589904133216712961)
            ·
              refine ⟨65476214692428099912534721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87301619589904133216712961 65476214692428099912534721)
              ·
                refine ⟨49107161019321074934401041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65476214692428099912534721 49107161019321074934401041)
                ·
                  refine ⟨36830370764490806200800781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49107161019321074934401041 36830370764490806200800781)
                  ·
                    refine ⟨13811389036684052325300293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36830370764490806200800781 13811389036684052325300293)
                    ·
                      refine ⟨2589635444378259810993805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13811389036684052325300293 2589635444378259810993805)
                      ·
                        rfl

theorem cell23_5043297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_5043297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043297 prefixEnd_5043297 := by exact prefixLift 5043297
  have htrace : WordTrace (prefixWord ++ tailWord_5043297) baseStart_5043297 baseEnd_5043297 := by
    simpa [prefixWord, tailWord_5043297, baseEnd_5043297] using wordTrace_append hprefix tailTrace_5043297
  have hstable : (prefixWord ++ tailWord_5043297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043297).length < 2 ^ (prefixWord ++ tailWord_5043297).sum := by decide
  have hdescent : baseEnd_5043297 < baseStart_5043297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043318 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5043318 : Nat := 118140960795 + 5043318 * 2 ^ 59
def prefixEnd_5043318 : Nat := 4983230072969 + 3 ^ 40 * 5043318 * 2
def baseEnd_5043318 : Nat := 2589646227472004228831209

theorem tailTrace_5043318 : CollatzResearch.WordTrace tailWord_5043318 prefixEnd_5043318 2589646227472004228831209 := by
  unfold tailWord_5043318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496557446432980686594663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122629946095285127323676405 11496557446432980686594663)
  ·
    refine ⟨17244836169649471029891995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11496557446432980686594663 17244836169649471029891995)
    ·
      refine ⟨25867254254474206544837993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17244836169649471029891995 25867254254474206544837993)
      ·
        refine ⟨19400440690855654908628495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25867254254474206544837993 19400440690855654908628495)
        ·
          refine ⟨29100661036283482362942743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19400440690855654908628495 29100661036283482362942743)
          ·
            refine ⟨43650991554425223544414115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29100661036283482362942743 43650991554425223544414115)
            ·
              refine ⟨65476487331637835316621173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43650991554425223544414115 65476487331637835316621173)
              ·
                refine ⟨6138420687341047060933235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65476487331637835316621173 6138420687341047060933235)
                ·
                  refine ⟨9207631031011570591399853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138420687341047060933235 9207631031011570591399853)
                  ·
                    refine ⟨3452861636629338971774945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9207631031011570591399853 3452861636629338971774945)
                    ·
                      refine ⟨2589646227472004228831209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452861636629338971774945 2589646227472004228831209)
                      ·
                        rfl

theorem cell23_5043318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5043318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043318 prefixEnd_5043318 := by exact prefixLift 5043318
  have htrace : WordTrace (prefixWord ++ tailWord_5043318) baseStart_5043318 baseEnd_5043318 := by
    simpa [prefixWord, tailWord_5043318, baseEnd_5043318] using wordTrace_append hprefix tailTrace_5043318
  have hstable : (prefixWord ++ tailWord_5043318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043318).length < 2 ^ (prefixWord ++ tailWord_5043318).sum := by decide
  have hdescent : baseEnd_5043318 < baseStart_5043318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043326 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5043326 : Nat := 118140960795 + 5043326 * 2 ^ 59
def prefixEnd_5043326 : Nat := 4983230072969 + 3 ^ 40 * 5043326 * 2
def baseEnd_5043326 : Nat := 2589650335317240197531173

theorem tailTrace_5043326 : CollatzResearch.WordTrace tailWord_5043326 prefixEnd_5043326 2589650335317240197531173 := by
  unfold tailWord_5043326
  simp only [CollatzResearch.WordTrace]
  refine ⟨22993151365862338543975729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122630140617932472234537221 22993151365862338543975729)
  ·
    refine ⟨17244863524396753907981797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22993151365862338543975729 17244863524396753907981797)
    ·
      refine ⟨3233411910824391357746587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17244863524396753907981797 3233411910824391357746587)
      ·
        refine ⟨4850117866236587036619881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233411910824391357746587 4850117866236587036619881)
        ·
          refine ⟨3637588399677440277464911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4850117866236587036619881 3637588399677440277464911)
          ·
            refine ⟨5456382599516160416197367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637588399677440277464911 5456382599516160416197367)
            ·
              refine ⟨8184573899274240624296051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456382599516160416197367 8184573899274240624296051)
              ·
                refine ⟨12276860848911360936444077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8184573899274240624296051 12276860848911360936444077)
                ·
                  refine ⟨4603822818341760351166529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12276860848911360936444077 4603822818341760351166529)
                  ·
                    refine ⟨3452867113756320263374897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603822818341760351166529 3452867113756320263374897)
                    ·
                      refine ⟨2589650335317240197531173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452867113756320263374897 2589650335317240197531173)
                      ·
                        rfl

theorem cell23_5043326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5043326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043326 prefixEnd_5043326 := by exact prefixLift 5043326
  have htrace : WordTrace (prefixWord ++ tailWord_5043326) baseStart_5043326 baseEnd_5043326 := by
    simpa [prefixWord, tailWord_5043326, baseEnd_5043326] using wordTrace_append hprefix tailTrace_5043326
  have hstable : (prefixWord ++ tailWord_5043326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043326).length < 2 ^ (prefixWord ++ tailWord_5043326).sum := by decide
  have hdescent : baseEnd_5043326 < baseStart_5043326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043331 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 4, 2, 2]
def baseStart_5043331 : Nat := 118140960795 + 5043331 * 2 ^ 59
def prefixEnd_5043331 : Nat := 4983230072969 + 3 ^ 40 * 5043331 * 2
def baseEnd_5043331 : Nat := 2589652902720512677968649

theorem tailTrace_5043331 : CollatzResearch.WordTrace tailWord_5043331 prefixEnd_5043331 2589652902720512677968649 := by
  unfold tailWord_5043331
  simp only [CollatzResearch.WordTrace]
  refine ⟨183945393291880594205737847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122630262194587062803825231 183945393291880594205737847)
  ·
    refine ⟨275918089937820891308606771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183945393291880594205737847 275918089937820891308606771)
    ·
      refine ⟨413877134906731336962910157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275918089937820891308606771 413877134906731336962910157)
      ·
        refine ⟨155203925590024251361091309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413877134906731336962910157 155203925590024251361091309)
        ·
          refine ⟨58201472096259094260409241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155203925590024251361091309 58201472096259094260409241)
          ·
            refine ⟨43651104072194320695306931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58201472096259094260409241 43651104072194320695306931)
            ·
              refine ⟨65476656108291481042960397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43651104072194320695306931 65476656108291481042960397)
              ·
                refine ⟨24553746040609305391110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65476656108291481042960397 24553746040609305391110149)
                ·
                  refine ⟨4603827382614244760833153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24553746040609305391110149 4603827382614244760833153)
                  ·
                    refine ⟨3452870536960683570624865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603827382614244760833153 3452870536960683570624865)
                    ·
                      refine ⟨2589652902720512677968649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452870536960683570624865 2589652902720512677968649)
                      ·
                        rfl

theorem cell23_5043331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_5043331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043331 prefixEnd_5043331 := by exact prefixLift 5043331
  have htrace : WordTrace (prefixWord ++ tailWord_5043331) baseStart_5043331 baseEnd_5043331 := by
    simpa [prefixWord, tailWord_5043331, baseEnd_5043331] using wordTrace_append hprefix tailTrace_5043331
  have hstable : (prefixWord ++ tailWord_5043331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043331).length < 2 ^ (prefixWord ++ tailWord_5043331).sum := by decide
  have hdescent : baseEnd_5043331 < baseStart_5043331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043388 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 5]
def baseStart_5043388 : Nat := 118140960795 + 5043388 * 2 ^ 59
def prefixEnd_5043388 : Nat := 4983230072969 + 3 ^ 40 * 5043388 * 2
def baseEnd_5043388 : Nat := 287742463457535439439543

theorem tailTrace_5043388 : CollatzResearch.WordTrace tailWord_5043388 prefixEnd_5043388 287742463457535439439543 := by
  unfold tailWord_5043388
  simp only [CollatzResearch.WordTrace]
  refine ⟨91973736126337046470281409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122631648168449395293708545 91973736126337046470281409)
  ·
    refine ⟨68980302094752784852711057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91973736126337046470281409 68980302094752784852711057)
    ·
      refine ⟨51735226571064588639533293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68980302094752784852711057 51735226571064588639533293)
      ·
        refine ⟨19400709964149220739824985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51735226571064588639533293 19400709964149220739824985)
        ·
          refine ⟨14550532473111915554868739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19400709964149220739824985 14550532473111915554868739)
          ·
            refine ⟨21825798709667873332303109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14550532473111915554868739 21825798709667873332303109)
            ·
              refine ⟨4092337258062726249806833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21825798709667873332303109 4092337258062726249806833)
              ·
                refine ⟨3069252943547044687355125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4092337258062726249806833 3069252943547044687355125)
                ·
                  refine ⟨287742463457535439439543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3069252943547044687355125 287742463457535439439543)
                  ·
                    rfl

theorem cell23_5043388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_5043388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043388 prefixEnd_5043388 := by exact prefixLift 5043388
  have htrace : WordTrace (prefixWord ++ tailWord_5043388) baseStart_5043388 baseEnd_5043388 := by
    simpa [prefixWord, tailWord_5043388, baseEnd_5043388] using wordTrace_append hprefix tailTrace_5043388
  have hstable : (prefixWord ++ tailWord_5043388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043388).length < 2 ^ (prefixWord ++ tailWord_5043388).sum := by decide
  have hdescent : baseEnd_5043388 < baseStart_5043388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043397 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_5043397 : Nat := 118140960795 + 5043397 * 2 ^ 59
def prefixEnd_5043397 : Nat := 4983230072969 + 3 ^ 40 * 5043397 * 2
def baseEnd_5043397 : Nat := 863228930814569806581115

theorem tailTrace_5043397 : CollatzResearch.WordTrace tailWord_5043397 prefixEnd_5043397 863228930814569806581115 := by
  unfold tailWord_5043397
  simp only [CollatzResearch.WordTrace]
  refine ⟨183947800509641487477640445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122631867006427658318426963 183947800509641487477640445)
  ·
    refine ⟨68980425191115557804115167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183947800509641487477640445 68980425191115557804115167)
    ·
      refine ⟨103470637786673336706172751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68980425191115557804115167 103470637786673336706172751)
      ·
        refine ⟨155205956680010005059259127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103470637786673336706172751 155205956680010005059259127)
        ·
          refine ⟨232808935020015007588888691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155205956680010005059259127 232808935020015007588888691)
          ·
            refine ⟨349213402530022511383333037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232808935020015007588888691 349213402530022511383333037)
            ·
              refine ⟨130955025948758441768749889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349213402530022511383333037 130955025948758441768749889)
              ·
                refine ⟨98216269461568831326562417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130955025948758441768749889 98216269461568831326562417)
                ·
                  refine ⟨73662202096176623494921813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98216269461568831326562417 73662202096176623494921813)
                  ·
                    refine ⟨863228930814569806581115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73662202096176623494921813 863228930814569806581115)
                    ·
                      rfl

theorem cell23_5043397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_5043397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043397 prefixEnd_5043397 := by exact prefixLift 5043397
  have htrace : WordTrace (prefixWord ++ tailWord_5043397) baseStart_5043397 baseEnd_5043397 := by
    simpa [prefixWord, tailWord_5043397, baseEnd_5043397] using wordTrace_append hprefix tailTrace_5043397
  have hstable : (prefixWord ++ tailWord_5043397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043397).length < 2 ^ (prefixWord ++ tailWord_5043397).sum := by decide
  have hdescent : baseEnd_5043397 < baseStart_5043397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043434 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5043434 : Nat := 118140960795 + 5043434 * 2 ^ 59
def prefixEnd_5043434 : Nat := 4983230072969 + 3 ^ 40 * 5043434 * 2
def baseEnd_5043434 : Nat := 2589705791227925774980675

theorem tailTrace_5043434 : CollatzResearch.WordTrace tailWord_5043434 prefixEnd_5043434 2589705791227925774980675 := by
  unfold tailWord_5043434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45987287502626860699184339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122632766673671628531158237 45987287502626860699184339)
  ·
    refine ⟨68980931253940291048776509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45987287502626860699184339 68980931253940291048776509)
    ·
      refine ⟨25867849220227609143291191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68980931253940291048776509 25867849220227609143291191)
      ·
        refine ⟨38801773830341413714936787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25867849220227609143291191 38801773830341413714936787)
        ·
          refine ⟨58202660745512120572405181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38801773830341413714936787 58202660745512120572405181)
          ·
            refine ⟨21825997779567045214651943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58202660745512120572405181 21825997779567045214651943)
            ·
              refine ⟨32738996669350567821977915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21825997779567045214651943 32738996669350567821977915)
              ·
                refine ⟨49108495004025851732966873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32738996669350567821977915 49108495004025851732966873)
                ·
                  refine ⟨36831371253019388799725155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49108495004025851732966873 36831371253019388799725155)
                  ·
                    refine ⟨55247056879529083199587733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36831371253019388799725155 55247056879529083199587733)
                    ·
                      refine ⟨2589705791227925774980675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55247056879529083199587733 2589705791227925774980675)
                      ·
                        rfl

theorem cell23_5043434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5043434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043434 prefixEnd_5043434 := by exact prefixLift 5043434
  have htrace : WordTrace (prefixWord ++ tailWord_5043434) baseStart_5043434 baseEnd_5043434 := by
    simpa [prefixWord, tailWord_5043434, baseEnd_5043434] using wordTrace_append hprefix tailTrace_5043434
  have hstable : (prefixWord ++ tailWord_5043434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043434).length < 2 ^ (prefixWord ++ tailWord_5043434).sum := by decide
  have hdescent : baseEnd_5043434 < baseStart_5043434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043461 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 6]
def baseStart_5043461 : Nat := 118140960795 + 5043461 * 2 ^ 59
def prefixEnd_5043461 : Nat := 4983230072969 + 3 ^ 40 * 5043461 * 2
def baseEnd_5043461 : Nat := 287746628356177463260339

theorem tailTrace_5043461 : CollatzResearch.WordTrace tailWord_5043461 prefixEnd_5043461 287746628356177463260339 := by
  unfold tailWord_5043461
  simp only [CollatzResearch.WordTrace]
  refine ⟨183950134781409626407970237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122633423187606417605313491 183950134781409626407970237)
  ·
    refine ⟨68981300543028609902988839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183950134781409626407970237 68981300543028609902988839)
    ·
      refine ⟨103471950814542914854483259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68981300543028609902988839 103471950814542914854483259)
      ·
        refine ⟨155207926221814372281724889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103471950814542914854483259 155207926221814372281724889)
        ·
          refine ⟨116405944666360779211293667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155207926221814372281724889 116405944666360779211293667)
          ·
            refine ⟨174608916999541168816940501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116405944666360779211293667 174608916999541168816940501)
            ·
              refine ⟨4092396492176746144147043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 174608916999541168816940501 4092396492176746144147043)
              ·
                refine ⟨6138594738265119216220565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092396492176746144147043 6138594738265119216220565)
                ·
                  refine ⟨287746628356177463260339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6138594738265119216220565 287746628356177463260339)
                  ·
                    rfl

theorem cell23_5043461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_5043461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043461 prefixEnd_5043461 := by exact prefixLift 5043461
  have htrace : WordTrace (prefixWord ++ tailWord_5043461) baseStart_5043461 baseEnd_5043461 := by
    simpa [prefixWord, tailWord_5043461, baseEnd_5043461] using wordTrace_append hprefix tailTrace_5043461
  have hstable : (prefixWord ++ tailWord_5043461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043461).length < 2 ^ (prefixWord ++ tailWord_5043461).sum := by decide
  have hdescent : baseEnd_5043461 < baseStart_5043461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043481 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 8, 3, 2]
def baseStart_5043481 : Nat := 118140960795 + 5043481 * 2 ^ 59
def prefixEnd_5043481 : Nat := 4983230072969 + 3 ^ 40 * 5043481 * 2
def baseEnd_5043481 : Nat := 2589729924818687091092959

theorem tailTrace_5043481 : CollatzResearch.WordTrace tailWord_5043481 prefixEnd_5043481 2589729924818687091092959 := by
  unfold tailWord_5043481
  simp only [CollatzResearch.WordTrace]
  refine ⟨183950864241337169823698297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122633909494224779882465531 183950864241337169823698297)
  ·
    refine ⟨137963148181002877367773723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183950864241337169823698297 137963148181002877367773723)
    ·
      refine ⟨206944722271504316051660585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137963148181002877367773723 206944722271504316051660585)
      ·
        refine ⟨155208541703628237038745439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206944722271504316051660585 155208541703628237038745439)
        ·
          refine ⟨232812812555442355558118159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155208541703628237038745439 232812812555442355558118159)
          ·
            refine ⟨349219218833163533337177239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232812812555442355558118159 349219218833163533337177239)
            ·
              refine ⟨523828828249745300005765859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349219218833163533337177239 523828828249745300005765859)
              ·
                refine ⟨785743242374617950008648789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523828828249745300005765859 785743242374617950008648789)
                ·
                  refine ⟨9207928621577554101663853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 785743242374617950008648789 9207928621577554101663853)
                  ·
                    refine ⟨3452973233091582788123945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9207928621577554101663853 3452973233091582788123945)
                    ·
                      refine ⟨2589729924818687091092959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3452973233091582788123945 2589729924818687091092959)
                      ·
                        rfl

theorem cell23_5043481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_5043481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043481 prefixEnd_5043481 := by exact prefixLift 5043481
  have htrace : WordTrace (prefixWord ++ tailWord_5043481) baseStart_5043481 baseEnd_5043481 := by
    simpa [prefixWord, tailWord_5043481, baseEnd_5043481] using wordTrace_append hprefix tailTrace_5043481
  have hstable : (prefixWord ++ tailWord_5043481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043481).length < 2 ^ (prefixWord ++ tailWord_5043481).sum := by decide
  have hdescent : baseEnd_5043481 < baseStart_5043481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043491 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 1, 5]
def baseStart_5043491 : Nat := 118140960795 + 5043491 * 2 ^ 59
def prefixEnd_5043491 : Nat := 4983230072969 + 3 ^ 40 * 5043491 * 2
def baseEnd_5043491 : Nat := 863245019875077350655971

theorem tailTrace_5043491 : CollatzResearch.WordTrace tailWord_5043491 prefixEnd_5043491 863245019875077350655971 := by
  unfold tailWord_5043491
  simp only [CollatzResearch.WordTrace]
  refine ⟨183951228971300941531562327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122634152647533961021041551 183951228971300941531562327)
  ·
    refine ⟨275926843456951412297343491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183951228971300941531562327 275926843456951412297343491)
    ·
      refine ⟨413890265185427118446015237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275926843456951412297343491 413890265185427118446015237)
      ·
        refine ⟨77604424722267584708627857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 413890265185427118446015237 77604424722267584708627857)
        ·
          refine ⟨58203318541700688531470893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77604424722267584708627857 58203318541700688531470893)
          ·
            refine ⟨21826244453137758199301585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58203318541700688531470893 21826244453137758199301585)
            ·
              refine ⟨16369683339853318649476189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21826244453137758199301585 16369683339853318649476189)
              ·
                refine ⟨6138631252444994493553571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16369683339853318649476189 6138631252444994493553571)
                ·
                  refine ⟨9207946878667491740330357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138631252444994493553571 9207946878667491740330357)
                  ·
                    refine ⟨863245019875077350655971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9207946878667491740330357 863245019875077350655971)
                    ·
                      rfl

theorem cell23_5043491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 5].length) (baseStart_5043491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043491 prefixEnd_5043491 := by exact prefixLift 5043491
  have htrace : WordTrace (prefixWord ++ tailWord_5043491) baseStart_5043491 baseEnd_5043491 := by
    simpa [prefixWord, tailWord_5043491, baseEnd_5043491] using wordTrace_append hprefix tailTrace_5043491
  have hstable : (prefixWord ++ tailWord_5043491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043491).length < 2 ^ (prefixWord ++ tailWord_5043491).sum := by decide
  have hdescent : baseEnd_5043491 < baseStart_5043491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043505 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_5043505 : Nat := 118140960795 + 5043505 * 2 ^ 59
def prefixEnd_5043505 : Nat := 4983230072969 + 3 ^ 40 * 5043505 * 2
def baseEnd_5043505 : Nat := 2589742248354394997192849

theorem tailTrace_5043505 : CollatzResearch.WordTrace tailWord_5043505 prefixEnd_5043505 2589742248354394997192849 := by
  unfold tailWord_5043505
  simp only [CollatzResearch.WordTrace]
  refine ⟨183951739593250221922571969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122634493062166814615047979 183951739593250221922571969)
  ·
    refine ⟨137963804694937666441928977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183951739593250221922571969 137963804694937666441928977)
    ·
      refine ⟨103472853521203249831446733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137963804694937666441928977 103472853521203249831446733)
      ·
        refine ⟨38802320070451218686792525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103472853521203249831446733 38802320070451218686792525)
        ·
          refine ⟨14550870026419207007547197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38802320070451218686792525 14550870026419207007547197)
          ·
            refine ⟨5456576259907202627830199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14550870026419207007547197 5456576259907202627830199)
            ·
              refine ⟨8184864389860803941745299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456576259907202627830199 8184864389860803941745299)
              ·
                refine ⟨12277296584791205912617949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8184864389860803941745299 12277296584791205912617949)
                ·
                  refine ⟨4603986219296702217231731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12277296584791205912617949 4603986219296702217231731)
                  ·
                    refine ⟨6905979328945053325847597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4603986219296702217231731 6905979328945053325847597)
                    ·
                      refine ⟨2589742248354394997192849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6905979328945053325847597 2589742248354394997192849)
                      ·
                        rfl

theorem cell23_5043505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_5043505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043505 prefixEnd_5043505 := by exact prefixLift 5043505
  have htrace : WordTrace (prefixWord ++ tailWord_5043505) baseStart_5043505 baseEnd_5043505 := by
    simpa [prefixWord, tailWord_5043505, baseEnd_5043505] using wordTrace_append hprefix tailTrace_5043505
  have hstable : (prefixWord ++ tailWord_5043505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043505).length < 2 ^ (prefixWord ++ tailWord_5043505).sum := by decide
  have hdescent : baseEnd_5043505 < baseStart_5043505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043528 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_5043528 : Nat := 118140960795 + 5043528 * 2 ^ 59
def prefixEnd_5043528 : Nat := 4983230072969 + 3 ^ 40 * 5043528 * 2
def baseEnd_5043528 : Nat := 2589754058409448407205243

theorem tailTrace_5043528 : CollatzResearch.WordTrace tailWord_5043528 prefixEnd_5043528 2589754058409448407205243 := by
  unfold tailWord_5043528
  simp only [CollatzResearch.WordTrace]
  refine ⟨91976289236083448425329619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122635052314777931233772825 91976289236083448425329619)
  ·
    refine ⟨137964433854125172637994429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91976289236083448425329619 137964433854125172637994429)
    ·
      refine ⟨51736662695296939739247911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137964433854125172637994429 51736662695296939739247911)
      ·
        refine ⟨77604994042945409608871867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51736662695296939739247911 77604994042945409608871867)
        ·
          refine ⟨116407491064418114413307801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77604994042945409608871867 116407491064418114413307801)
          ·
            refine ⟨87305618298313585809980851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116407491064418114413307801 87305618298313585809980851)
            ·
              refine ⟨130958427447470378714971277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87305618298313585809980851 130958427447470378714971277)
              ·
                refine ⟨49109410292801392018114229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130958427447470378714971277 49109410292801392018114229)
                ·
                  refine ⟨4604007214950130501698209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49109410292801392018114229 4604007214950130501698209)
                  ·
                    refine ⟨3453005411212597876273657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604007214950130501698209 3453005411212597876273657)
                    ·
                      refine ⟨2589754058409448407205243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453005411212597876273657 2589754058409448407205243)
                      ·
                        rfl

theorem cell23_5043528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_5043528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043528 prefixEnd_5043528 := by exact prefixLift 5043528
  have htrace : WordTrace (prefixWord ++ tailWord_5043528) baseStart_5043528 baseEnd_5043528 := by
    simpa [prefixWord, tailWord_5043528, baseEnd_5043528] using wordTrace_append hprefix tailTrace_5043528
  have hstable : (prefixWord ++ tailWord_5043528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043528).length < 2 ^ (prefixWord ++ tailWord_5043528).sum := by decide
  have hdescent : baseEnd_5043528 < baseStart_5043528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043534 : List Nat := [4, 1, 1, 1, 1, 1, 3, 11]
def baseStart_5043534 : Nat := 118140960795 + 5043534 * 2 ^ 59
def prefixEnd_5043534 : Nat := 4983230072969 + 3 ^ 40 * 5043534 * 2
def baseEnd_5043534 : Nat := 95916931084939829027045

theorem tailTrace_5043534 : CollatzResearch.WordTrace tailWord_5043534 prefixEnd_5043534 95916931084939829027045 := by
  unfold tailWord_5043534
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994099663768144984422207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122635198206763439916918437 22994099663768144984422207)
  ·
    refine ⟨34491149495652217476633311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22994099663768144984422207 34491149495652217476633311)
    ·
      refine ⟨51736724243478326214949967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34491149495652217476633311 51736724243478326214949967)
      ·
        refine ⟨77605086365217489322424951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51736724243478326214949967 77605086365217489322424951)
        ·
          refine ⟨116407629547826233983637427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77605086365217489322424951 116407629547826233983637427)
          ·
            refine ⟨174611444321739350975456141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116407629547826233983637427 174611444321739350975456141)
            ·
              refine ⟨65479291620652256615796053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174611444321739350975456141 65479291620652256615796053)
              ·
                refine ⟨95916931084939829027045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65479291620652256615796053 95916931084939829027045)
                ·
                  rfl

theorem cell23_5043534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_5043534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043534 prefixEnd_5043534 := by exact prefixLift 5043534
  have htrace : WordTrace (prefixWord ++ tailWord_5043534) baseStart_5043534 baseEnd_5043534 := by
    simpa [prefixWord, tailWord_5043534, baseEnd_5043534] using wordTrace_append hprefix tailTrace_5043534
  have hstable : (prefixWord ++ tailWord_5043534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043534).length < 2 ^ (prefixWord ++ tailWord_5043534).sum := by decide
  have hdescent : baseEnd_5043534 < baseStart_5043534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043541 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5043541 : Nat := 118140960795 + 5043541 * 2 ^ 59
def prefixEnd_5043541 : Nat := 4983230072969 + 3 ^ 40 * 5043541 * 2
def baseEnd_5043541 : Nat := 2589760733657956856342683

theorem tailTrace_5043541 : CollatzResearch.WordTrace tailWord_5043541 prefixEnd_5043541 2589760733657956856342683 := by
  unfold tailWord_5043541
  simp only [CollatzResearch.WordTrace]
  refine ⟨183953052621119800070882477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122635368414079866713921651 183953052621119800070882477)
  ·
    refine ⟨68982394732919925026580929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183953052621119800070882477 68982394732919925026580929)
    ·
      refine ⟨51736796049689943769935697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68982394732919925026580929 51736796049689943769935697)
      ·
        refine ⟨38802597037267457827451773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51736796049689943769935697 38802597037267457827451773)
        ·
          refine ⟨14550973888975296685294415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38802597037267457827451773 14550973888975296685294415)
          ·
            refine ⟨21826460833462945027941623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14550973888975296685294415 21826460833462945027941623)
            ·
              refine ⟨32739691250194417541912435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21826460833462945027941623 32739691250194417541912435)
              ·
                refine ⟨49109536875291626312868653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32739691250194417541912435 49109536875291626312868653)
                ·
                  refine ⟨18416076328234359867325745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49109536875291626312868653 18416076328234359867325745)
                  ·
                    refine ⟨13812057246175769900494309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18416076328234359867325745 13812057246175769900494309)
                    ·
                      refine ⟨2589760733657956856342683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13812057246175769900494309 2589760733657956856342683)
                      ·
                        rfl

theorem cell23_5043541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5043541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043541 prefixEnd_5043541 := by exact prefixLift 5043541
  have htrace : WordTrace (prefixWord ++ tailWord_5043541) baseStart_5043541 baseEnd_5043541 := by
    simpa [prefixWord, tailWord_5043541, baseEnd_5043541] using wordTrace_append hprefix tailTrace_5043541
  have hstable : (prefixWord ++ tailWord_5043541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043541).length < 2 ^ (prefixWord ++ tailWord_5043541).sum := by decide
  have hdescent : baseEnd_5043541 < baseStart_5043541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043571 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 9, 2]
def baseStart_5043571 : Nat := 118140960795 + 5043571 * 2 ^ 59
def prefixEnd_5043571 : Nat := 4983230072969 + 3 ^ 40 * 5043571 * 2
def baseEnd_5043571 : Nat := 2589776138077591738967545

theorem tailTrace_5043571 : CollatzResearch.WordTrace tailWord_5043571 prefixEnd_5043571 2589776138077591738967545 := by
  unfold tailWord_5043571
  simp only [CollatzResearch.WordTrace]
  refine ⟨183954146811011115194474567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122636097874007410129649711 183954146811011115194474567)
  ·
    refine ⟨275931220216516672791711851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183954146811011115194474567 275931220216516672791711851)
    ·
      refine ⟨413896830324775009187567777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275931220216516672791711851 413896830324775009187567777)
      ·
        refine ⟨310422622743581256890675833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413896830324775009187567777 310422622743581256890675833)
        ·
          refine ⟨232816967057685942668006875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310422622743581256890675833 232816967057685942668006875)
          ·
            refine ⟨349225450586528914002010313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232816967057685942668006875 349225450586528914002010313)
            ·
              refine ⟨261919087939896685501507735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349225450586528914002010313 261919087939896685501507735)
              ·
                refine ⟨392878631909845028252261603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261919087939896685501507735 392878631909845028252261603)
                ·
                  refine ⟨589317947864767542378392405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392878631909845028252261603 589317947864767542378392405)
                  ·
                    refine ⟨3453034850770122318623393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 589317947864767542378392405 3453034850770122318623393)
                    ·
                      refine ⟨2589776138077591738967545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453034850770122318623393 2589776138077591738967545)
                      ·
                        rfl

theorem cell23_5043571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9, 2].length) (baseStart_5043571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043571 prefixEnd_5043571 := by exact prefixLift 5043571
  have htrace : WordTrace (prefixWord ++ tailWord_5043571) baseStart_5043571 baseEnd_5043571 := by
    simpa [prefixWord, tailWord_5043571, baseEnd_5043571] using wordTrace_append hprefix tailTrace_5043571
  have hstable : (prefixWord ++ tailWord_5043571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043571).length < 2 ^ (prefixWord ++ tailWord_5043571).sum := by decide
  have hdescent : baseEnd_5043571 < baseStart_5043571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043612 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5043612 : Nat := 118140960795 + 5043612 * 2 ^ 59
def prefixEnd_5043612 : Nat := 4983230072969 + 3 ^ 40 * 5043612 * 2
def baseEnd_5043612 : Nat := 2589797190784426078554857

theorem tailTrace_5043612 : CollatzResearch.WordTrace tailWord_5043612 prefixEnd_5043612 2589797190784426078554857 := by
  unfold tailWord_5043612
  simp only [CollatzResearch.WordTrace]
  refine ⟨91977821101931289598358545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122637094802575052797811393 91977821101931289598358545)
  ·
    refine ⟨68983365826448467198768909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91977821101931289598358545 68983365826448467198768909)
    ·
      refine ⟨25868762184918175199538341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68983365826448467198768909 25868762184918175199538341)
      ·
        refine ⟨4850392909672157849913439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25868762184918175199538341 4850392909672157849913439)
        ·
          refine ⟨7275589364508236774870159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850392909672157849913439 7275589364508236774870159)
          ·
            refine ⟨10913384046762355162305239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275589364508236774870159 10913384046762355162305239)
            ·
              refine ⟨16370076070143532743457859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10913384046762355162305239 16370076070143532743457859)
              ·
                refine ⟨24555114105215299115186789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16370076070143532743457859 24555114105215299115186789)
                ·
                  refine ⟨4604083894727868584097523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24555114105215299115186789 4604083894727868584097523)
                  ·
                    refine ⟨6906125842091802876146285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604083894727868584097523 6906125842091802876146285)
                    ·
                      refine ⟨2589797190784426078554857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906125842091802876146285 2589797190784426078554857)
                      ·
                        rfl

theorem cell23_5043612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5043612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043612 prefixEnd_5043612 := by exact prefixLift 5043612
  have htrace : WordTrace (prefixWord ++ tailWord_5043612) baseStart_5043612 baseEnd_5043612 := by
    simpa [prefixWord, tailWord_5043612, baseEnd_5043612] using wordTrace_append hprefix tailTrace_5043612
  have hstable : (prefixWord ++ tailWord_5043612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043612).length < 2 ^ (prefixWord ++ tailWord_5043612).sum := by decide
  have hdescent : baseEnd_5043612 < baseStart_5043612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043621 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_5043621 : Nat := 118140960795 + 5043621 * 2 ^ 59
def prefixEnd_5043621 : Nat := 4983230072969 + 3 ^ 40 * 5043621 * 2
def baseEnd_5043621 : Nat := 2589801812110316543342315

theorem tailTrace_5043621 : CollatzResearch.WordTrace tailWord_5043621 prefixEnd_5043621 2589801812110316543342315 := by
  unfold tailWord_5043621
  simp only [CollatzResearch.WordTrace]
  refine ⟨183955970460829973733794717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122637313640553315822529811 183955970460829973733794717)
  ·
    refine ⟨68983488922811240150173019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183955970460829973733794717 68983488922811240150173019)
    ·
      refine ⟨103475233384216860225259529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68983488922811240150173019 103475233384216860225259529)
      ·
        refine ⟨77606425038162645168944647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103475233384216860225259529 77606425038162645168944647)
        ·
          refine ⟨116409637557243967753416971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77606425038162645168944647 116409637557243967753416971)
          ·
            refine ⟨174614456335865951630125457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116409637557243967753416971 174614456335865951630125457)
            ·
              refine ⟨130960842251899463722594093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174614456335865951630125457 130960842251899463722594093)
              ·
                refine ⟨49110315844462298895972785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130960842251899463722594093 49110315844462298895972785)
                ·
                  refine ⟨36832736883346724171979589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49110315844462298895972785 36832736883346724171979589)
                  ·
                    refine ⟨6906138165627510782246173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36832736883346724171979589 6906138165627510782246173)
                    ·
                      refine ⟨2589801812110316543342315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906138165627510782246173 2589801812110316543342315)
                      ·
                        rfl

theorem cell23_5043621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_5043621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043621 prefixEnd_5043621 := by exact prefixLift 5043621
  have htrace : WordTrace (prefixWord ++ tailWord_5043621) baseStart_5043621 baseEnd_5043621 := by
    simpa [prefixWord, tailWord_5043621, baseEnd_5043621] using wordTrace_append hprefix tailTrace_5043621
  have hstable : (prefixWord ++ tailWord_5043621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043621).length < 2 ^ (prefixWord ++ tailWord_5043621).sum := by decide
  have hdescent : baseEnd_5043621 < baseStart_5043621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043629 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5043629 : Nat := 118140960795 + 5043629 * 2 ^ 59
def prefixEnd_5043629 : Nat := 4983230072969 + 3 ^ 40 * 5043629 * 2
def baseEnd_5043629 : Nat := 2589805919955552512042279

theorem tailTrace_5043629 : CollatzResearch.WordTrace tailWord_5043629 prefixEnd_5043629 2589805919955552512042279 := by
  unfold tailWord_5043629
  simp only [CollatzResearch.WordTrace]
  refine ⟨183956262244800991100085941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122637508163200660733390627 183956262244800991100085941)
  ·
    refine ⟨17245899585450092915633057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183956262244800991100085941 17245899585450092915633057)
    ·
      refine ⟨12934424689087569686724793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17245899585450092915633057 12934424689087569686724793)
      ·
        refine ⟨9700818516815677265043595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12934424689087569686724793 9700818516815677265043595)
        ·
          refine ⟨14551227775223515897565393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9700818516815677265043595 14551227775223515897565393)
          ·
            refine ⟨10913420831417636923174045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14551227775223515897565393 10913420831417636923174045)
            ·
              refine ⟨4092532811781613846190267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10913420831417636923174045 4092532811781613846190267)
              ·
                refine ⟨6138799217672420769285401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092532811781613846190267 6138799217672420769285401)
                ·
                  refine ⟨4604099413254315576964051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138799217672420769285401 4604099413254315576964051)
                  ·
                    refine ⟨6906149119881473365446077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604099413254315576964051 6906149119881473365446077)
                    ·
                      refine ⟨2589805919955552512042279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906149119881473365446077 2589805919955552512042279)
                      ·
                        rfl

theorem cell23_5043629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5043629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043629 prefixEnd_5043629 := by exact prefixLift 5043629
  have htrace : WordTrace (prefixWord ++ tailWord_5043629) baseStart_5043629 baseEnd_5043629 := by
    simpa [prefixWord, tailWord_5043629, baseEnd_5043629] using wordTrace_append hprefix tailTrace_5043629
  have hstable : (prefixWord ++ tailWord_5043629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043629).length < 2 ^ (prefixWord ++ tailWord_5043629).sum := by decide
  have hdescent : baseEnd_5043629 < baseStart_5043629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043635 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 2, 2, 2]
def baseStart_5043635 : Nat := 118140960795 + 5043635 * 2 ^ 59
def prefixEnd_5043635 : Nat := 4983230072969 + 3 ^ 40 * 5043635 * 2
def baseEnd_5043635 : Nat := 2589809000839479488567251

theorem tailTrace_5043635 : CollatzResearch.WordTrace tailWord_5043635 prefixEnd_5043635 2589809000839479488567251 := by
  unfold tailWord_5043635
  simp only [CollatzResearch.WordTrace]
  refine ⟨183956481082779254124804359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122637654055186169416536239 183956481082779254124804359)
  ·
    refine ⟨275934721624168881187206539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183956481082779254124804359 275934721624168881187206539)
    ·
      refine ⟨413902082436253321780809809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275934721624168881187206539 413902082436253321780809809)
      ·
        refine ⟨310426561827189991335607357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413902082436253321780809809 310426561827189991335607357)
        ·
          refine ⟨116409960685196246750852759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310426561827189991335607357 116409960685196246750852759)
          ·
            refine ⟨174614941027794370126279139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116409960685196246750852759 174614941027794370126279139)
            ·
              refine ⟨261922411541691555189418709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174614941027794370126279139 261922411541691555189418709)
              ·
                refine ⟨6138806520508395824752001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 261922411541691555189418709 6138806520508395824752001)
                ·
                  refine ⟨4604104890381296868564001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138806520508395824752001 4604104890381296868564001)
                  ·
                    refine ⟨3453078667785972651423001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604104890381296868564001 3453078667785972651423001)
                    ·
                      refine ⟨2589809000839479488567251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453078667785972651423001 2589809000839479488567251)
                      ·
                        rfl

theorem cell23_5043635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2, 2].length) (baseStart_5043635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043635 prefixEnd_5043635 := by exact prefixLift 5043635
  have htrace : WordTrace (prefixWord ++ tailWord_5043635) baseStart_5043635 baseEnd_5043635 := by
    simpa [prefixWord, tailWord_5043635, baseEnd_5043635] using wordTrace_append hprefix tailTrace_5043635
  have hstable : (prefixWord ++ tailWord_5043635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043635).length < 2 ^ (prefixWord ++ tailWord_5043635).sum := by decide
  have hdescent : baseEnd_5043635 < baseStart_5043635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043651 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3]
def baseStart_5043651 : Nat := 118140960795 + 5043651 * 2 ^ 59
def prefixEnd_5043651 : Nat := 4983230072969 + 3 ^ 40 * 5043651 * 2
def baseEnd_5043651 : Nat := 2589817216529951425967177

theorem tailTrace_5043651 : CollatzResearch.WordTrace tailWord_5043651 prefixEnd_5043651 2589817216529951425967177 := by
  unfold tailWord_5043651
  simp only [CollatzResearch.WordTrace]
  refine ⟨183957064650721288857386807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122638043100480859238257871 183957064650721288857386807)
  ·
    refine ⟨275935596976081933286080211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183957064650721288857386807 275935596976081933286080211)
    ·
      refine ⟨413903395464122899929120317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275935596976081933286080211 413903395464122899929120317)
      ·
        refine ⟨155213773299046087473420119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413903395464122899929120317 155213773299046087473420119)
        ·
          refine ⟨232820659948569131210130179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155213773299046087473420119 232820659948569131210130179)
          ·
            refine ⟨349230989922853696815195269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232820659948569131210130179 349230989922853696815195269)
            ·
              refine ⟨65480810610535068152849113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 349230989922853696815195269 65480810610535068152849113)
              ·
                refine ⟨49110607957901301114636835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65480810610535068152849113 49110607957901301114636835)
                ·
                  refine ⟨73665911936851951671955253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49110607957901301114636835 73665911936851951671955253)
                  ·
                    refine ⟨6906179244079870469245805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73665911936851951671955253 6906179244079870469245805)
                    ·
                      refine ⟨2589817216529951425967177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906179244079870469245805 2589817216529951425967177)
                      ·
                        rfl

theorem cell23_5043651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_5043651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043651 prefixEnd_5043651 := by exact prefixLift 5043651
  have htrace : WordTrace (prefixWord ++ tailWord_5043651) baseStart_5043651 baseEnd_5043651 := by
    simpa [prefixWord, tailWord_5043651, baseEnd_5043651] using wordTrace_append hprefix tailTrace_5043651
  have hstable : (prefixWord ++ tailWord_5043651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043651).length < 2 ^ (prefixWord ++ tailWord_5043651).sum := by decide
  have hdescent : baseEnd_5043651 < baseStart_5043651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043652 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5043652 : Nat := 118140960795 + 5043652 * 2 ^ 59
def prefixEnd_5043652 : Nat := 4983230072969 + 3 ^ 40 * 5043652 * 2
def baseEnd_5043652 : Nat := 2589817730010605922054673

theorem tailTrace_5043652 : CollatzResearch.WordTrace tailWord_5043652 prefixEnd_5043652 2589817730010605922054673 := by
  unfold tailWord_5043652
  simp only [CollatzResearch.WordTrace]
  refine ⟨91978550561858833014086605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122638067415811777352115473 91978550561858833014086605)
  ·
    refine ⟨34491956460697062380282477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91978550561858833014086605 34491956460697062380282477)
    ·
      refine ⟨12934483672761398392605929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34491956460697062380282477 12934483672761398392605929)
      ·
        refine ⟨9700862754571048794454447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12934483672761398392605929 9700862754571048794454447)
        ·
          refine ⟨14551294131856573191681671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9700862754571048794454447 14551294131856573191681671)
          ·
            refine ⟨21826941197784859787522507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14551294131856573191681671 21826941197784859787522507)
            ·
              refine ⟨32740411796677289681283761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21826941197784859787522507 32740411796677289681283761)
              ·
                refine ⟨24555308847507967260962821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32740411796677289681283761 24555308847507967260962821)
                ·
                  refine ⟨4604120408907743861430529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24555308847507967260962821 4604120408907743861430529)
                  ·
                    refine ⟨3453090306680807896072897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604120408907743861430529 3453090306680807896072897)
                    ·
                      refine ⟨2589817730010605922054673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453090306680807896072897 2589817730010605922054673)
                      ·
                        rfl

theorem cell23_5043652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5043652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043652 prefixEnd_5043652 := by exact prefixLift 5043652
  have htrace : WordTrace (prefixWord ++ tailWord_5043652) baseStart_5043652 baseEnd_5043652 := by
    simpa [prefixWord, tailWord_5043652, baseEnd_5043652] using wordTrace_append hprefix tailTrace_5043652
  have hstable : (prefixWord ++ tailWord_5043652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043652).length < 2 ^ (prefixWord ++ tailWord_5043652).sum := by decide
  have hdescent : baseEnd_5043652 < baseStart_5043652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043681 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_5043681 : Nat := 118140960795 + 5043681 * 2 ^ 59
def prefixEnd_5043681 : Nat := 4983230072969 + 3 ^ 40 * 5043681 * 2
def baseEnd_5043681 : Nat := 2589832620949586308592039

theorem tailTrace_5043681 : CollatzResearch.WordTrace tailWord_5043681 prefixEnd_5043681 2589832620949586308592039 := by
  unfold tailWord_5043681
  simp only [CollatzResearch.WordTrace]
  refine ⟨183958158840612603980978897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122638772560408402653985931 183958158840612603980978897)
  ·
    refine ⟨137968619130459452985734173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183958158840612603980978897 137968619130459452985734173)
    ·
      refine ⟨51738232173922294869650315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137968619130459452985734173 51738232173922294869650315)
      ·
        refine ⟨77607348260883442304475473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51738232173922294869650315 77607348260883442304475473)
        ·
          refine ⟨58205511195662581728356605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77607348260883442304475473 58205511195662581728356605)
          ·
            refine ⟨21827066698373468148133727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58205511195662581728356605 21827066698373468148133727)
            ·
              refine ⟨32740600047560202222200591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21827066698373468148133727 32740600047560202222200591)
              ·
                refine ⟨49110900071340303333300887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32740600047560202222200591 49110900071340303333300887)
                ·
                  refine ⟨73666350107010454999951331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49110900071340303333300887 73666350107010454999951331)
                  ·
                    refine ⟨110499525160515682499926997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73666350107010454999951331 110499525160515682499926997)
                    ·
                      refine ⟨2589832620949586308592039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110499525160515682499926997 2589832620949586308592039)
                      ·
                        rfl

theorem cell23_5043681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_5043681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043681 prefixEnd_5043681 := by exact prefixLift 5043681
  have htrace : WordTrace (prefixWord ++ tailWord_5043681) baseStart_5043681 baseEnd_5043681 := by
    simpa [prefixWord, tailWord_5043681, baseEnd_5043681] using wordTrace_append hprefix tailTrace_5043681
  have hstable : (prefixWord ++ tailWord_5043681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043681).length < 2 ^ (prefixWord ++ tailWord_5043681).sum := by decide
  have hdescent : baseEnd_5043681 < baseStart_5043681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043691 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_5043691 : Nat := 118140960795 + 5043691 * 2 ^ 59
def prefixEnd_5043691 : Nat := 4983230072969 + 3 ^ 40 * 5043691 * 2
def baseEnd_5043691 : Nat := 2589837755756131269466993

theorem tailTrace_5043691 : CollatzResearch.WordTrace tailWord_5043691 prefixEnd_5043691 2589837755756131269466993 := by
  unfold tailWord_5043691
  simp only [CollatzResearch.WordTrace]
  refine ⟨183958523570576375688842927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122639015713717583792561951 183958523570576375688842927)
  ·
    refine ⟨275937785355864563533264391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183958523570576375688842927 275937785355864563533264391)
    ·
      refine ⟨413906678033796845299896587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275937785355864563533264391 413906678033796845299896587)
      ·
        refine ⟨620860017050695267949844881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413906678033796845299896587 620860017050695267949844881)
        ·
          refine ⟨465645012788021450962383661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620860017050695267949844881 465645012788021450962383661)
          ·
            refine ⟨174616879795508044110893873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465645012788021450962383661 174616879795508044110893873)
            ·
              refine ⟨130962659846631033083170405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174616879795508044110893873 130962659846631033083170405)
              ·
                refine ⟨24555498721243318703094451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130962659846631033083170405 24555498721243318703094451)
                ·
                  refine ⟨36833248081864978054641677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24555498721243318703094451 36833248081864978054641677)
                  ·
                    refine ⟨13812468030699366770490629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36833248081864978054641677 13812468030699366770490629)
                    ·
                      refine ⟨2589837755756131269466993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13812468030699366770490629 2589837755756131269466993)
                      ·
                        rfl

theorem cell23_5043691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_5043691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043691 prefixEnd_5043691 := by exact prefixLift 5043691
  have htrace : WordTrace (prefixWord ++ tailWord_5043691) baseStart_5043691 baseEnd_5043691 := by
    simpa [prefixWord, tailWord_5043691, baseEnd_5043691] using wordTrace_append hprefix tailTrace_5043691
  have hstable : (prefixWord ++ tailWord_5043691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043691).length < 2 ^ (prefixWord ++ tailWord_5043691).sum := by decide
  have hdescent : baseEnd_5043691 < baseStart_5043691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043708 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_5043708 : Nat := 118140960795 + 5043708 * 2 ^ 59
def prefixEnd_5043708 : Nat := 4983230072969 + 3 ^ 40 * 5043708 * 2
def baseEnd_5043708 : Nat := 2589846484927257702954415

theorem tailTrace_5043708 : CollatzResearch.WordTrace tailWord_5043708 prefixEnd_5043708 2589846484927257702954415 := by
  unfold tailWord_5043708
  simp only [CollatzResearch.WordTrace]
  refine ⟨91979571805757393796105889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122639429074343191728141185 91979571805757393796105889)
  ·
    refine ⟨68984678854318045347079417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91979571805757393796105889 68984678854318045347079417)
    ·
      refine ⟨51738509140738534010309563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68984678854318045347079417 51738509140738534010309563)
      ·
        refine ⟨77607763711107801015464345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51738509140738534010309563 77607763711107801015464345)
        ·
          refine ⟨58205822783330850761598259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77607763711107801015464345 58205822783330850761598259)
          ·
            refine ⟨87308734174996276142397389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58205822783330850761598259 87308734174996276142397389)
            ·
              refine ⟨32740775315623603553399021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87308734174996276142397389 32740775315623603553399021)
              ·
                refine ⟨12277790743358851332524633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32740775315623603553399021 12277790743358851332524633)
                ·
                  refine ⟨9208343057519138499393475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12277790743358851332524633 9208343057519138499393475)
                  ·
                    refine ⟨13812514586278707749090213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9208343057519138499393475 13812514586278707749090213)
                    ·
                      refine ⟨2589846484927257702954415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13812514586278707749090213 2589846484927257702954415)
                      ·
                        rfl

theorem cell23_5043708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_5043708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043708 prefixEnd_5043708 := by exact prefixLift 5043708
  have htrace : WordTrace (prefixWord ++ tailWord_5043708) baseStart_5043708 baseEnd_5043708 := by
    simpa [prefixWord, tailWord_5043708, baseEnd_5043708] using wordTrace_append hprefix tailTrace_5043708
  have hstable : (prefixWord ++ tailWord_5043708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043708).length < 2 ^ (prefixWord ++ tailWord_5043708).sum := by decide
  have hdescent : baseEnd_5043708 < baseStart_5043708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043721 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_5043721 : Nat := 118140960795 + 5043721 * 2 ^ 59
def prefixEnd_5043721 : Nat := 4983230072969 + 3 ^ 40 * 5043721 * 2
def baseEnd_5043721 : Nat := 2589853160175766152091855

theorem tailTrace_5043721 : CollatzResearch.WordTrace tailWord_5043721 prefixEnd_5043721 2589853160175766152091855 := by
  unfold tailWord_5043721
  simp only [CollatzResearch.WordTrace]
  refine ⟨183959617760467690812435017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122639745173645127208290011 183959617760467690812435017)
  ·
    refine ⟨137969713320350768109326263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183959617760467690812435017 137969713320350768109326263)
    ·
      refine ⟨206954569980526152163989395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137969713320350768109326263 206954569980526152163989395)
      ·
        refine ⟨310431854970789228245984093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206954569980526152163989395 310431854970789228245984093)
        ·
          refine ⟨116411945614045960592244035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310431854970789228245984093 116411945614045960592244035)
          ·
            refine ⟨174617918421068940888366053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116411945614045960592244035 174617918421068940888366053)
            ·
              refine ⟨32740859703950426416568635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174617918421068940888366053 32740859703950426416568635)
              ·
                refine ⟨49111289555925639624852953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32740859703950426416568635 49111289555925639624852953)
                ·
                  refine ⟨36833467166944229718639715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49111289555925639624852953 36833467166944229718639715)
                  ·
                    refine ⟨55250200750416344577959573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36833467166944229718639715 55250200750416344577959573)
                    ·
                      refine ⟨2589853160175766152091855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55250200750416344577959573 2589853160175766152091855)
                      ·
                        rfl

theorem cell23_5043721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_5043721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043721 prefixEnd_5043721 := by exact prefixLift 5043721
  have htrace : WordTrace (prefixWord ++ tailWord_5043721) baseStart_5043721 baseEnd_5043721 := by
    simpa [prefixWord, tailWord_5043721, baseEnd_5043721] using wordTrace_append hprefix tailTrace_5043721
  have hstable : (prefixWord ++ tailWord_5043721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043721).length < 2 ^ (prefixWord ++ tailWord_5043721).sum := by decide
  have hdescent : baseEnd_5043721 < baseStart_5043721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043752 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5043752 : Nat := 118140960795 + 5043752 * 2 ^ 59
def prefixEnd_5043752 : Nat := 4983230072969 + 3 ^ 40 * 5043752 * 2
def baseEnd_5043752 : Nat := 863289692692018510268071

theorem tailTrace_5043752 : CollatzResearch.WordTrace tailWord_5043752 prefixEnd_5043752 863289692692018510268071 := by
  unfold tailWord_5043752
  simp only [CollatzResearch.WordTrace]
  refine ⟨91980374211677691553406755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122640498948903588737875673 91980374211677691553406755)
  ·
    refine ⟨137970561317516537330110133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91980374211677691553406755 137970561317516537330110133)
    ·
      refine ⟨12934740123517175374697825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137970561317516537330110133 12934740123517175374697825)
      ·
        refine ⟨9701055092637881531023369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12934740123517175374697825 9701055092637881531023369)
        ·
          refine ⟨7275791319478411148267527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9701055092637881531023369 7275791319478411148267527)
          ·
            refine ⟨10913686979217616722401291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275791319478411148267527 10913686979217616722401291)
            ·
              refine ⟨16370530468826425083601937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10913686979217616722401291 16370530468826425083601937)
              ·
                refine ⟨12277897851619818812701453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16370530468826425083601937 12277897851619818812701453)
                ·
                  refine ⟨4604211694357432054763045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12277897851619818812701453 4604211694357432054763045)
                  ·
                    refine ⟨863289692692018510268071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4604211694357432054763045 863289692692018510268071)
                    ·
                      rfl

theorem cell23_5043752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5043752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043752 prefixEnd_5043752 := by exact prefixLift 5043752
  have htrace : WordTrace (prefixWord ++ tailWord_5043752) baseStart_5043752 baseEnd_5043752 := by
    simpa [prefixWord, tailWord_5043752, baseEnd_5043752] using wordTrace_append hprefix tailTrace_5043752
  have hstable : (prefixWord ++ tailWord_5043752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043752).length < 2 ^ (prefixWord ++ tailWord_5043752).sum := by decide
  have hdescent : baseEnd_5043752 < baseStart_5043752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043782 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5043782 : Nat := 118140960795 + 5043782 * 2 ^ 59
def prefixEnd_5043782 : Nat := 4983230072969 + 3 ^ 40 * 5043782 * 2
def baseEnd_5043782 : Nat := 287764942499521157047675

theorem tailTrace_5043782 : CollatzResearch.WordTrace tailWord_5043782 prefixEnd_5043782 287764942499521157047675 := by
  unfold tailWord_5043782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748807581663959319700175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122641228408831132153603733 5748807581663959319700175)
  ·
    refine ⟨8623211372495938979550263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748807581663959319700175 8623211372495938979550263)
    ·
      refine ⟨12934817058743908469325395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623211372495938979550263 12934817058743908469325395)
      ·
        refine ⟨19402225588115862703988093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12934817058743908469325395 19402225588115862703988093)
        ·
          refine ⟨7275834595543448513995535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19402225588115862703988093 7275834595543448513995535)
          ·
            refine ⟨10913751893315172770993303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7275834595543448513995535 10913751893315172770993303)
            ·
              refine ⟨16370627839972759156489955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10913751893315172770993303 16370627839972759156489955)
              ·
                refine ⟨24555941759959138734734933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16370627839972759156489955 24555941759959138734734933)
                ·
                  refine ⟨287764942499521157047675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24555941759959138734734933 287764942499521157047675)
                  ·
                    rfl

theorem cell23_5043782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5043782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043782 prefixEnd_5043782 := by exact prefixLift 5043782
  have htrace : WordTrace (prefixWord ++ tailWord_5043782) baseStart_5043782 baseEnd_5043782 := by
    simpa [prefixWord, tailWord_5043782, baseEnd_5043782] using wordTrace_append hprefix tailTrace_5043782
  have hstable : (prefixWord ++ tailWord_5043782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043782).length < 2 ^ (prefixWord ++ tailWord_5043782).sum := by decide
  have hdescent : baseEnd_5043782 < baseStart_5043782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043785 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 2, 3, 2]
def baseStart_5043785 : Nat := 118140960795 + 5043785 * 2 ^ 59
def prefixEnd_5043785 : Nat := 4983230072969 + 3 ^ 40 * 5043785 * 2
def baseEnd_5043785 : Nat := 2589886022937653901691561

theorem tailTrace_5043785 : CollatzResearch.WordTrace tailWord_5043785 prefixEnd_5043785 2589886022937653901691561 := by
  unfold tailWord_5043785
  simp only [CollatzResearch.WordTrace]
  refine ⟨183961952032235829742764809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122641301354823886495176539 183961952032235829742764809)
  ·
    refine ⟨137971464024176872307073607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183961952032235829742764809 137971464024176872307073607)
    ·
      refine ⟨206957196036265308460610411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137971464024176872307073607 206957196036265308460610411)
      ·
        refine ⟨310435794054397962690915617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206957196036265308460610411 310435794054397962690915617)
        ·
          refine ⟨232826845540798472018186713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310435794054397962690915617 232826845540798472018186713)
          ·
            refine ⟨174620134155598854013640035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232826845540798472018186713 174620134155598854013640035)
            ·
              refine ⟨261930201233398281020460053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174620134155598854013640035 261930201233398281020460053)
              ·
                refine ⟨12277978182815544422834065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261930201233398281020460053 12277978182815544422834065)
                ·
                  refine ⟨9208483637111658317125549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12277978182815544422834065 9208483637111658317125549)
                  ·
                    refine ⟨3453181363916871868922081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9208483637111658317125549 3453181363916871868922081)
                    ·
                      refine ⟨2589886022937653901691561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453181363916871868922081 2589886022937653901691561)
                      ·
                        rfl

theorem cell23_5043785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3, 2].length) (baseStart_5043785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043785 prefixEnd_5043785 := by exact prefixLift 5043785
  have htrace : WordTrace (prefixWord ++ tailWord_5043785) baseStart_5043785 baseEnd_5043785 := by
    simpa [prefixWord, tailWord_5043785, baseEnd_5043785] using wordTrace_append hprefix tailTrace_5043785
  have hstable : (prefixWord ++ tailWord_5043785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043785).length < 2 ^ (prefixWord ++ tailWord_5043785).sum := by decide
  have hdescent : baseEnd_5043785 < baseStart_5043785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043792 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 1, 1, 3]
def baseStart_5043792 : Nat := 118140960795 + 5043792 * 2 ^ 59
def prefixEnd_5043792 : Nat := 4983230072969 + 3 ^ 40 * 5043792 * 2
def baseEnd_5043792 : Nat := 2589889617302235374304029

theorem tailTrace_5043792 : CollatzResearch.WordTrace tailWord_5043792 prefixEnd_5043792 2589889617302235374304029 := by
  unfold tailWord_5043792
  simp only [CollatzResearch.WordTrace]
  refine ⟨91981103671605234969134815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122641471562140313292179753 91981103671605234969134815)
  ·
    refine ⟨137971655507407852453702223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91981103671605234969134815 137971655507407852453702223)
    ·
      refine ⟨206957483261111778680553335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137971655507407852453702223 206957483261111778680553335)
      ·
        refine ⟨310436224891667668020830003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206957483261111778680553335 310436224891667668020830003)
        ·
          refine ⟨465654337337501502031245005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310436224891667668020830003 465654337337501502031245005)
          ·
            refine ⟨174620376501563063261716877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465654337337501502031245005 174620376501563063261716877)
            ·
              refine ⟨65482641188086148723143829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174620376501563063261716877 65482641188086148723143829)
              ·
                refine ⟨3069498805691538221397367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65482641188086148723143829 3069498805691538221397367)
                ·
                  refine ⟨4604248208537307332096051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069498805691538221397367 4604248208537307332096051)
                  ·
                    refine ⟨6906372312805960998144077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604248208537307332096051 6906372312805960998144077)
                    ·
                      refine ⟨2589889617302235374304029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906372312805960998144077 2589889617302235374304029)
                      ·
                        rfl

theorem cell23_5043792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 1, 3].length) (baseStart_5043792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043792 prefixEnd_5043792 := by exact prefixLift 5043792
  have htrace : WordTrace (prefixWord ++ tailWord_5043792) baseStart_5043792 baseEnd_5043792 := by
    simpa [prefixWord, tailWord_5043792, baseEnd_5043792] using wordTrace_append hprefix tailTrace_5043792
  have hstable : (prefixWord ++ tailWord_5043792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043792).length < 2 ^ (prefixWord ++ tailWord_5043792).sum := by decide
  have hdescent : baseEnd_5043792 < baseStart_5043792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043815 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_5043815 : Nat := 118140960795 + 5043815 * 2 ^ 59
def prefixEnd_5043815 : Nat := 4983230072969 + 3 ^ 40 * 5043815 * 2
def baseEnd_5043815 : Nat := 2589901427357288784316423

theorem tailTrace_5043815 : CollatzResearch.WordTrace tailWord_5043815 prefixEnd_5043815 2589901427357288784316423 := by
  unfold tailWord_5043815
  simp only [CollatzResearch.WordTrace]
  refine ⟨183963046222127144866356899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122642030814751429910904599 183963046222127144866356899)
  ·
    refine ⟨275944569333190717299535349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183963046222127144866356899 275944569333190717299535349)
    ·
      refine ⟨25869803374986629746831439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275944569333190717299535349 25869803374986629746831439)
      ·
        refine ⟨38804705062479944620247159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25869803374986629746831439 38804705062479944620247159)
        ·
          refine ⟨58207057593719916930370739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38804705062479944620247159 58207057593719916930370739)
          ·
            refine ⟨87310586390579875395556109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58207057593719916930370739 87310586390579875395556109)
            ·
              refine ⟨32741469896467453273333541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87310586390579875395556109 32741469896467453273333541)
              ·
                refine ⟨6139025605587647488750039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32741469896467453273333541 6139025605587647488750039)
                ·
                  refine ⟨9208538408381471233125059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139025605587647488750039 9208538408381471233125059)
                  ·
                    refine ⟨13812807612572206849687589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9208538408381471233125059 13812807612572206849687589)
                    ·
                      refine ⟨2589901427357288784316423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13812807612572206849687589 2589901427357288784316423)
                      ·
                        rfl

theorem cell23_5043815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_5043815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043815 prefixEnd_5043815 := by exact prefixLift 5043815
  have htrace : WordTrace (prefixWord ++ tailWord_5043815) baseStart_5043815 baseEnd_5043815 := by
    simpa [prefixWord, tailWord_5043815, baseEnd_5043815] using wordTrace_append hprefix tailTrace_5043815
  have hstable : (prefixWord ++ tailWord_5043815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043815).length < 2 ^ (prefixWord ++ tailWord_5043815).sum := by decide
  have hdescent : baseEnd_5043815 < baseStart_5043815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043826 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5043826 : Nat := 118140960795 + 5043826 * 2 ^ 59
def prefixEnd_5043826 : Nat := 4983230072969 + 3 ^ 40 * 5043826 * 2
def baseEnd_5043826 : Nat := 2589907075644488241278873

theorem tailTrace_5043826 : CollatzResearch.WordTrace tailWord_5043826 prefixEnd_5043826 2589907075644488241278873 := by
  unfold tailWord_5043826
  simp only [CollatzResearch.WordTrace]
  refine ⟨45990861856271823436251833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122642298283391529163338221 45990861856271823436251833)
  ·
    refine ⟨34493146392203867577188875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45990861856271823436251833 34493146392203867577188875)
    ·
      refine ⟨51739719588305801365783313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34493146392203867577188875 51739719588305801365783313)
      ·
        refine ⟨38804789691229351024337485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51739719588305801365783313 38804789691229351024337485)
        ·
          refine ⟨14551796134211006634126557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38804789691229351024337485 14551796134211006634126557)
          ·
            refine ⟨5456923550329127487797459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14551796134211006634126557 5456923550329127487797459)
            ·
              refine ⟨8185385325493691231696189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456923550329127487797459 8185385325493691231696189)
              ·
                refine ⟨3069519497060134211886071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8185385325493691231696189 3069519497060134211886071)
                ·
                  refine ⟨4604279245590201317829107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069519497060134211886071 4604279245590201317829107)
                  ·
                    refine ⟨6906418868385301976743661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604279245590201317829107 6906418868385301976743661)
                    ·
                      refine ⟨2589907075644488241278873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906418868385301976743661 2589907075644488241278873)
                      ·
                        rfl

theorem cell23_5043826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5043826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043826 prefixEnd_5043826 := by exact prefixLift 5043826
  have htrace : WordTrace (prefixWord ++ tailWord_5043826) baseStart_5043826 baseEnd_5043826 := by
    simpa [prefixWord, tailWord_5043826, baseEnd_5043826] using wordTrace_append hprefix tailTrace_5043826
  have hstable : (prefixWord ++ tailWord_5043826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043826).length < 2 ^ (prefixWord ++ tailWord_5043826).sum := by decide
  have hdescent : baseEnd_5043826 < baseStart_5043826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043835 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 3]
def baseStart_5043835 : Nat := 118140960795 + 5043835 * 2 ^ 59
def prefixEnd_5043835 : Nat := 4983230072969 + 3 ^ 40 * 5043835 * 2
def baseEnd_5043835 : Nat := 2589911696970378706066331

theorem tailTrace_5043835 : CollatzResearch.WordTrace tailWord_5043835 prefixEnd_5043835 2589911696970378706066331 := by
  unfold tailWord_5043835
  simp only [CollatzResearch.WordTrace]
  refine ⟨183963775682054688282084959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122642517121369792188056639 183963775682054688282084959)
  ·
    refine ⟨275945663523082032423127439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183963775682054688282084959 275945663523082032423127439)
    ·
      refine ⟨413918495284623048634691159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275945663523082032423127439 413918495284623048634691159)
      ·
        refine ⟨620877742926934572952036739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413918495284623048634691159 620877742926934572952036739)
        ·
          refine ⟨931316614390401859428055109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620877742926934572952036739 931316614390401859428055109)
          ·
            refine ⟨174621865198200348642760333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 931316614390401859428055109 174621865198200348642760333)
            ·
              refine ⟨65483199449325130741035125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174621865198200348642760333 65483199449325130741035125)
              ·
                refine ⟨6139049948374231006972043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65483199449325130741035125 6139049948374231006972043)
                ·
                  refine ⟨9208574922561346510458065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139049948374231006972043 9208574922561346510458065)
                  ·
                    refine ⟨6906431191921009882843549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9208574922561346510458065 6906431191921009882843549)
                    ·
                      refine ⟨2589911696970378706066331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906431191921009882843549 2589911696970378706066331)
                      ·
                        rfl

theorem cell23_5043835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 3].length) (baseStart_5043835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043835 prefixEnd_5043835 := by exact prefixLift 5043835
  have htrace : WordTrace (prefixWord ++ tailWord_5043835) baseStart_5043835 baseEnd_5043835 := by
    simpa [prefixWord, tailWord_5043835, baseEnd_5043835] using wordTrace_append hprefix tailTrace_5043835
  have hstable : (prefixWord ++ tailWord_5043835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043835).length < 2 ^ (prefixWord ++ tailWord_5043835).sum := by decide
  have hdescent : baseEnd_5043835 < baseStart_5043835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043849 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 1, 2, 2]
def baseStart_5043849 : Nat := 118140960795 + 5043849 * 2 ^ 59
def prefixEnd_5043849 : Nat := 4983230072969 + 3 ^ 40 * 5043849 * 2
def baseEnd_5043849 : Nat := 2589918885699541651291267

theorem tailTrace_5043849 : CollatzResearch.WordTrace tailWord_5043849 prefixEnd_5043849 2589918885699541651291267 := by
  unfold tailWord_5043849
  simp only [CollatzResearch.WordTrace]
  refine ⟨183964286304003968673094601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122642857536002645782063067 183964286304003968673094601)
  ·
    refine ⟨137973214728002976504820951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183964286304003968673094601 137973214728002976504820951)
    ·
      refine ⟨206959822092004464757231427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137973214728002976504820951 206959822092004464757231427)
      ·
        refine ⟨310439733138006697135847141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206959822092004464757231427 310439733138006697135847141)
        ·
          refine ⟨58207449963376255712971339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310439733138006697135847141 58207449963376255712971339)
          ·
            refine ⟨87311174945064383569457009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58207449963376255712971339 87311174945064383569457009)
            ·
              refine ⟨65483381208798287677092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87311174945064383569457009 65483381208798287677092757)
              ·
                refine ⟨3069533494162419734863723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65483381208798287677092757 3069533494162419734863723)
                ·
                  refine ⟨4604300241243629602295585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069533494162419734863723 4604300241243629602295585)
                  ·
                    refine ⟨3453225180932722201721689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604300241243629602295585 3453225180932722201721689)
                    ·
                      refine ⟨2589918885699541651291267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453225180932722201721689 2589918885699541651291267)
                      ·
                        rfl

theorem cell23_5043849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 2, 2].length) (baseStart_5043849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043849 prefixEnd_5043849 := by exact prefixLift 5043849
  have htrace : WordTrace (prefixWord ++ tailWord_5043849) baseStart_5043849 baseEnd_5043849 := by
    simpa [prefixWord, tailWord_5043849, baseEnd_5043849] using wordTrace_append hprefix tailTrace_5043849
  have hstable : (prefixWord ++ tailWord_5043849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043849).length < 2 ^ (prefixWord ++ tailWord_5043849).sum := by decide
  have hdescent : baseEnd_5043849 < baseStart_5043849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043865 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 3]
def baseStart_5043865 : Nat := 118140960795 + 5043865 * 2 ^ 59
def prefixEnd_5043865 : Nat := 4983230072969 + 3 ^ 40 * 5043865 * 2
def baseEnd_5043865 : Nat := 2589927101390013588691193

theorem tailTrace_5043865 : CollatzResearch.WordTrace tailWord_5043865 prefixEnd_5043865 2589927101390013588691193 := by
  unfold tailWord_5043865
  simp only [CollatzResearch.WordTrace]
  refine ⟨183964869871946003405677049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122643246581297335603784699 183964869871946003405677049)
  ·
    refine ⟨137973652403959502554257787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183964869871946003405677049 137973652403959502554257787)
    ·
      refine ⟨206960478605939253831386681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137973652403959502554257787 206960478605939253831386681)
      ·
        refine ⟨155220358954454440373540011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206960478605939253831386681 155220358954454440373540011)
        ·
          refine ⟨232830538431681660560310017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155220358954454440373540011 232830538431681660560310017)
          ·
            refine ⟨174622903823761245420232513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232830538431681660560310017 174622903823761245420232513)
            ·
              refine ⟨130967177867820934065174385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174622903823761245420232513 130967177867820934065174385)
              ·
                refine ⟨98225383400865700548880789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130967177867820934065174385 98225383400865700548880789)
                ·
                  refine ⟨4604314846915579713228787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98225383400865700548880789 4604314846915579713228787)
                  ·
                    refine ⟨6906472270373369569843181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604314846915579713228787 6906472270373369569843181)
                    ·
                      refine ⟨2589927101390013588691193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906472270373369569843181 2589927101390013588691193)
                      ·
                        rfl

theorem cell23_5043865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_5043865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043865 prefixEnd_5043865 := by exact prefixLift 5043865
  have htrace : WordTrace (prefixWord ++ tailWord_5043865) baseStart_5043865 baseEnd_5043865 := by
    simpa [prefixWord, tailWord_5043865, baseEnd_5043865] using wordTrace_append hprefix tailTrace_5043865
  have hstable : (prefixWord ++ tailWord_5043865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043865).length < 2 ^ (prefixWord ++ tailWord_5043865).sum := by decide
  have hdescent : baseEnd_5043865 < baseStart_5043865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043886 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5043886 : Nat := 118140960795 + 5043886 * 2 ^ 59
def prefixEnd_5043886 : Nat := 4983230072969 + 3 ^ 40 * 5043886 * 2
def baseEnd_5043886 : Nat := 2589937884483758006528597

theorem tailTrace_5043886 : CollatzResearch.WordTrace tailWord_5043886 prefixEnd_5043886 2589937884483758006528597 := by
  unfold tailWord_5043886
  simp only [CollatzResearch.WordTrace]
  refine ⟨22995704475608740499023939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122643757203246615994794341 22995704475608740499023939)
  ·
    refine ⟨34493556713413110748535909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22995704475608740499023939 34493556713413110748535909)
    ·
      refine ⟨6467541883764958265350483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34493556713413110748535909 6467541883764958265350483)
      ·
        refine ⟨9701312825647437398025725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6467541883764958265350483 9701312825647437398025725)
        ·
          refine ⟨3637992309617789024259647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9701312825647437398025725 3637992309617789024259647)
          ·
            refine ⟨5456988464426683536389471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637992309617789024259647 5456988464426683536389471)
            ·
              refine ⟨8185482696640025304584207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5456988464426683536389471 8185482696640025304584207)
              ·
                refine ⟨12278224044960037956876311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8185482696640025304584207 12278224044960037956876311)
                ·
                  refine ⟨18417336067440056935314467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12278224044960037956876311 18417336067440056935314467)
                  ·
                    refine ⟨27626004101160085402971701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18417336067440056935314467 27626004101160085402971701)
                    ·
                      refine ⟨2589937884483758006528597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27626004101160085402971701 2589937884483758006528597)
                      ·
                        rfl

theorem cell23_5043886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5043886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043886 prefixEnd_5043886 := by exact prefixLift 5043886
  have htrace : WordTrace (prefixWord ++ tailWord_5043886) baseStart_5043886 baseEnd_5043886 := by
    simpa [prefixWord, tailWord_5043886, baseEnd_5043886] using wordTrace_append hprefix tailTrace_5043886
  have hstable : (prefixWord ++ tailWord_5043886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043886).length < 2 ^ (prefixWord ++ tailWord_5043886).sum := by decide
  have hdescent : baseEnd_5043886 < baseStart_5043886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043906 : List Nat := [3, 5, 1, 2, 1, 2, 1, 8]
def baseStart_5043906 : Nat := 118140960795 + 5043906 * 2 ^ 59
def prefixEnd_5043906 : Nat := 4983230072969 + 3 ^ 40 * 5043906 * 2
def baseEnd_5043906 : Nat := 95924005707290664010315

theorem tailTrace_5043906 : CollatzResearch.WordTrace tailWord_5043906 prefixEnd_5043906 95924005707290664010315 := by
  unfold tailWord_5043906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45991591316199366851979893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122644243509864978271946381 45991591316199366851979893)
  ·
    refine ⟨4311711685893690642373115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45991591316199366851979893 4311711685893690642373115)
    ·
      refine ⟨6467567528840535963559673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311711685893690642373115 6467567528840535963559673)
      ·
        refine ⟨4850675646630401972669755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6467567528840535963559673 4850675646630401972669755)
        ·
          refine ⟨7276013469945602959004633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850675646630401972669755 7276013469945602959004633)
          ·
            refine ⟨5457010102459202219253475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7276013469945602959004633 5457010102459202219253475)
            ·
              refine ⟨8185515153688803328880213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457010102459202219253475 8185515153688803328880213)
              ·
                refine ⟨95924005707290664010315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8185515153688803328880213 95924005707290664010315)
                ·
                  rfl

theorem cell23_5043906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_5043906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043906 prefixEnd_5043906 := by exact prefixLift 5043906
  have htrace : WordTrace (prefixWord ++ tailWord_5043906) baseStart_5043906 baseEnd_5043906 := by
    simpa [prefixWord, tailWord_5043906, baseEnd_5043906] using wordTrace_append hprefix tailTrace_5043906
  have hstable : (prefixWord ++ tailWord_5043906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043906).length < 2 ^ (prefixWord ++ tailWord_5043906).sum := by decide
  have hdescent : baseEnd_5043906 < baseStart_5043906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043955 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3]
def baseStart_5043955 : Nat := 118140960795 + 5043955 * 2 ^ 59
def prefixEnd_5043955 : Nat := 4983230072969 + 3 ^ 40 * 5043955 * 2
def baseEnd_5043955 : Nat := 2589973314648918236565779

theorem tailTrace_5043955 : CollatzResearch.WordTrace tailWord_5043955 prefixEnd_5043955 2589973314648918236565779 := by
  unfold tailWord_5043955
  simp only [CollatzResearch.WordTrace]
  refine ⟨183968152441619948776453319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122645434961079965850968879 183968152441619948776453319)
  ·
    refine ⟨275952228662429923164679979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183968152441619948776453319 275952228662429923164679979)
    ·
      refine ⟨413928342993644884747019969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275952228662429923164679979 413928342993644884747019969)
      ·
        refine ⟨310446257245233663560264977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413928342993644884747019969 310446257245233663560264977)
        ·
          refine ⟨232834692933925247670198733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310446257245233663560264977 232834692933925247670198733)
          ·
            refine ⟨87313009850221967876324525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232834692933925247670198733 87313009850221967876324525)
            ·
              refine ⟨32742378693833237953621697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87313009850221967876324525 32742378693833237953621697)
              ·
                refine ⟨24556784020374928465216273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32742378693833237953621697 24556784020374928465216273)
                ·
                  refine ⟨18417588015281196348912205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24556784020374928465216273 18417588015281196348912205)
                  ·
                    refine ⟨6906595505730448630842077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18417588015281196348912205 6906595505730448630842077)
                    ·
                      refine ⟨2589973314648918236565779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906595505730448630842077 2589973314648918236565779)
                      ·
                        rfl

theorem cell23_5043955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_5043955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043955 prefixEnd_5043955 := by exact prefixLift 5043955
  have htrace : WordTrace (prefixWord ++ tailWord_5043955) baseStart_5043955 baseEnd_5043955 := by
    simpa [prefixWord, tailWord_5043955, baseEnd_5043955] using wordTrace_append hprefix tailTrace_5043955
  have hstable : (prefixWord ++ tailWord_5043955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043955).length < 2 ^ (prefixWord ++ tailWord_5043955).sum := by decide
  have hdescent : baseEnd_5043955 < baseStart_5043955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043972 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5043972 : Nat := 118140960795 + 5043972 * 2 ^ 59
def prefixEnd_5043972 : Nat := 4983230072969 + 3 ^ 40 * 5043972 * 2
def baseEnd_5043972 : Nat := 2589982043820044670053201

theorem tailTrace_5043972 : CollatzResearch.WordTrace tailWord_5043972 prefixEnd_5043972 2589982043820044670053201 := by
  unfold tailWord_5043972
  simp only [CollatzResearch.WordTrace]
  refine ⟨91984386241279180339911085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122645848321705573786548113 91984386241279180339911085)
  ·
    refine ⟨34494144840479692627466657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91984386241279180339911085 34494144840479692627466657)
    ·
      refine ⟨25870608630359769470599993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34494144840479692627466657 25870608630359769470599993)
      ·
        refine ⟨19402956472769827102949995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25870608630359769470599993 19402956472769827102949995)
        ·
          refine ⟨29104434709154740654424993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19402956472769827102949995 29104434709154740654424993)
          ·
            refine ⟨21828326031866055490818745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29104434709154740654424993 21828326031866055490818745)
            ·
              refine ⟨16371244523899541618114059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21828326031866055490818745 16371244523899541618114059)
              ·
                refine ⟨24556866785849312427171089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16371244523899541618114059 24556866785849312427171089)
                ·
                  refine ⟨18417650089386984320378317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24556866785849312427171089 18417650089386984320378317)
                  ·
                    refine ⟨6906618783520119120141869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18417650089386984320378317 6906618783520119120141869)
                    ·
                      refine ⟨2589982043820044670053201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906618783520119120141869 2589982043820044670053201)
                      ·
                        rfl

theorem cell23_5043972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5043972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043972 prefixEnd_5043972 := by exact prefixLift 5043972
  have htrace : WordTrace (prefixWord ++ tailWord_5043972) baseStart_5043972 baseEnd_5043972 := by
    simpa [prefixWord, tailWord_5043972, baseEnd_5043972] using wordTrace_append hprefix tailTrace_5043972
  have hstable : (prefixWord ++ tailWord_5043972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043972).length < 2 ^ (prefixWord ++ tailWord_5043972).sum := by decide
  have hdescent : baseEnd_5043972 < baseStart_5043972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5043982 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5043982 : Nat := 118140960795 + 5043982 * 2 ^ 59
def prefixEnd_5043982 : Nat := 4983230072969 + 3 ^ 40 * 5043982 * 2
def baseEnd_5043982 : Nat := 2589987178626589630928155

theorem tailTrace_5043982 : CollatzResearch.WordTrace tailWord_5043982 prefixEnd_5043982 2589987178626589630928155 := by
  unfold tailWord_5043982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22996142151565266548460775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122646091475014754925124133 22996142151565266548460775)
  ·
    refine ⟨34494213227347899822691163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22996142151565266548460775 34494213227347899822691163)
    ·
      refine ⟨51741319841021849734036745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34494213227347899822691163 51741319841021849734036745)
      ·
        refine ⟨38805989880766387300527559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51741319841021849734036745 38805989880766387300527559)
        ·
          refine ⟨58208984821149580950791339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38805989880766387300527559 58208984821149580950791339)
          ·
            refine ⟨87313477231724371426187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58208984821149580950791339 87313477231724371426187009)
            ·
              refine ⟨65485107923793278569640257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87313477231724371426187009 65485107923793278569640257)
              ·
                refine ⟨49113830942844958927230193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65485107923793278569640257 49113830942844958927230193)
                ·
                  refine ⟨36835373207133719195422645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49113830942844958927230193 36835373207133719195422645)
                  ·
                    refine ⟨3453316238168786174570873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36835373207133719195422645 3453316238168786174570873)
                    ·
                      refine ⟨2589987178626589630928155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453316238168786174570873 2589987178626589630928155)
                      ·
                        rfl

theorem cell23_5043982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5043982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5043982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5043982 prefixEnd_5043982 := by exact prefixLift 5043982
  have htrace : WordTrace (prefixWord ++ tailWord_5043982) baseStart_5043982 baseEnd_5043982 := by
    simpa [prefixWord, tailWord_5043982, baseEnd_5043982] using wordTrace_append hprefix tailTrace_5043982
  have hstable : (prefixWord ++ tailWord_5043982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5043982).length < 2 ^ (prefixWord ++ tailWord_5043982).sum := by decide
  have hdescent : baseEnd_5043982 < baseStart_5043982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5043982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044012 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_5044012 : Nat := 118140960795 + 5044012 * 2 ^ 59
def prefixEnd_5044012 : Nat := 4983230072969 + 3 ^ 40 * 5044012 * 2
def baseEnd_5044012 : Nat := 2590002583046224513553017

theorem tailTrace_5044012 : CollatzResearch.WordTrace tailWord_5044012 prefixEnd_5044012 2590002583046224513553017 := by
  unfold tailWord_5044012
  simp only [CollatzResearch.WordTrace]
  refine ⟨91985115701206723755639145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122646820934942298340852193 91985115701206723755639145)
  ·
    refine ⟨68988836775905042816729359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91985115701206723755639145 68988836775905042816729359)
    ·
      refine ⟨103483255163857564225094039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68988836775905042816729359 103483255163857564225094039)
      ·
        refine ⟨155224882745786346337641059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103483255163857564225094039 155224882745786346337641059)
        ·
          refine ⟨232837324118679519506461589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155224882745786346337641059 232837324118679519506461589)
          ·
            refine ⟨10914249568063102476865387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 232837324118679519506461589 10914249568063102476865387)
            ·
              refine ⟨16371374352094653715298081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10914249568063102476865387 16371374352094653715298081)
              ·
                refine ⟨12278530764070990286473561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16371374352094653715298081 12278530764070990286473561)
                ·
                  refine ⟨9208898073053242714855171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12278530764070990286473561 9208898073053242714855171)
                  ·
                    refine ⟨13813347109579864072282757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9208898073053242714855171 13813347109579864072282757)
                    ·
                      refine ⟨2590002583046224513553017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13813347109579864072282757 2590002583046224513553017)
                      ·
                        rfl

theorem cell23_5044012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_5044012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044012 prefixEnd_5044012 := by exact prefixLift 5044012
  have htrace : WordTrace (prefixWord ++ tailWord_5044012) baseStart_5044012 baseEnd_5044012 := by
    simpa [prefixWord, tailWord_5044012, baseEnd_5044012] using wordTrace_append hprefix tailTrace_5044012
  have hstable : (prefixWord ++ tailWord_5044012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044012).length < 2 ^ (prefixWord ++ tailWord_5044012).sum := by decide
  have hdescent : baseEnd_5044012 < baseStart_5044012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044049 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_5044049 : Nat := 118140960795 + 5044049 * 2 ^ 59
def prefixEnd_5044049 : Nat := 4983230072969 + 3 ^ 40 * 5044049 * 2
def baseEnd_5044049 : Nat := 2590021581830440868790347

theorem tailTrace_5044049 : CollatzResearch.WordTrace tailWord_5044049 prefixEnd_5044049 2590021581830440868790347 := by
  unfold tailWord_5044049
  simp only [CollatzResearch.WordTrace]
  refine ⟨183971580903279402830375201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122647720602186268553583467 183971580903279402830375201)
  ·
    refine ⟨137978685677459552122781401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183971580903279402830375201 137978685677459552122781401)
    ·
      refine ⟨103484014258094664092086051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137978685677459552122781401 103484014258094664092086051)
      ·
        refine ⟨155226021387141996138129077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103484014258094664092086051 155226021387141996138129077)
        ·
          refine ⟨14552439505044562137949601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155226021387141996138129077 14552439505044562137949601)
          ·
            refine ⟨10914329628783421603462201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14552439505044562137949601 10914329628783421603462201)
            ·
              refine ⟨8185747221587566202596651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10914329628783421603462201 8185747221587566202596651)
              ·
                refine ⟨12278620832381349303894977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8185747221587566202596651 12278620832381349303894977)
                ·
                  refine ⟨9208965624286011977921233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12278620832381349303894977 9208965624286011977921233)
                  ·
                    refine ⟨6906724218214508983440925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9208965624286011977921233 6906724218214508983440925)
                    ·
                      refine ⟨2590021581830440868790347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6906724218214508983440925 2590021581830440868790347)
                      ·
                        rfl

theorem cell23_5044049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_5044049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044049 prefixEnd_5044049 := by exact prefixLift 5044049
  have htrace : WordTrace (prefixWord ++ tailWord_5044049) baseStart_5044049 baseEnd_5044049 := by
    simpa [prefixWord, tailWord_5044049, baseEnd_5044049] using wordTrace_append hprefix tailTrace_5044049
  have hstable : (prefixWord ++ tailWord_5044049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044049).length < 2 ^ (prefixWord ++ tailWord_5044049).sum := by decide
  have hdescent : baseEnd_5044049 < baseStart_5044049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044106 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5044106 : Nat := 118140960795 + 5044106 * 2 ^ 59
def prefixEnd_5044106 : Nat := 4983230072969 + 3 ^ 40 * 5044106 * 2
def baseEnd_5044106 : Nat := 2590050850227747145777585

theorem tailTrace_5044106 : CollatzResearch.WordTrace tailWord_5044106 prefixEnd_5044106 2590050850227747145777585 := by
  unfold tailWord_5044106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45993414966018225391300043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122649106576048601043466781 45993414966018225391300043)
  ·
    refine ⟨68990122449027338086950065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45993414966018225391300043 68990122449027338086950065)
    ·
      refine ⟨51742591836770503565212549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68990122449027338086950065 51742591836770503565212549)
      ·
        refine ⟨9701735969394469418477353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51742591836770503565212549 9701735969394469418477353)
        ·
          refine ⟨7276301977045852063858015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9701735969394469418477353 7276301977045852063858015)
          ·
            refine ⟨10914452965568778095787023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276301977045852063858015 10914452965568778095787023)
            ·
              refine ⟨16371679448353167143680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10914452965568778095787023 16371679448353167143680535)
              ·
                refine ⟨24557519172529750715520803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16371679448353167143680535 24557519172529750715520803)
                ·
                  refine ⟨36836278758794626073281205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24557519172529750715520803 36836278758794626073281205)
                  ·
                    refine ⟨3453401133636996194370113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36836278758794626073281205 3453401133636996194370113)
                    ·
                      refine ⟨2590050850227747145777585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453401133636996194370113 2590050850227747145777585)
                      ·
                        rfl

theorem cell23_5044106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5044106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044106 prefixEnd_5044106 := by exact prefixLift 5044106
  have htrace : WordTrace (prefixWord ++ tailWord_5044106) baseStart_5044106 baseEnd_5044106 := by
    simpa [prefixWord, tailWord_5044106, baseEnd_5044106] using wordTrace_append hprefix tailTrace_5044106
  have hstable : (prefixWord ++ tailWord_5044106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044106).length < 2 ^ (prefixWord ++ tailWord_5044106).sum := by decide
  have hdescent : baseEnd_5044106 < baseStart_5044106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044115 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_5044115 : Nat := 118140960795 + 5044115 * 2 ^ 59
def prefixEnd_5044115 : Nat := 4983230072969 + 3 ^ 40 * 5044115 * 2
def baseEnd_5044115 : Nat := 2590055471553637610565043

theorem tailTrace_5044115 : CollatzResearch.WordTrace tailWord_5044115 prefixEnd_5044115 2590055471553637610565043 := by
  unfold tailWord_5044115
  simp only [CollatzResearch.WordTrace]
  refine ⟨183973988121040296102277799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122649325414026864068185199 183973988121040296102277799)
  ·
    refine ⟨275960982181560444153416699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183973988121040296102277799 275960982181560444153416699)
    ·
      refine ⟨413941473272340666230125049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275960982181560444153416699 413941473272340666230125049)
      ·
        refine ⟨310456104954255499672593787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413941473272340666230125049 310456104954255499672593787)
        ·
          refine ⟨465684157431383249508890681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310456104954255499672593787 465684157431383249508890681)
          ·
            refine ⟨349263118073537437131668011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465684157431383249508890681 349263118073537437131668011)
            ·
              refine ⟨523894677110306155697502017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349263118073537437131668011 523894677110306155697502017)
              ·
                refine ⟨392921007832729616773126513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523894677110306155697502017 392921007832729616773126513)
                ·
                  refine ⟨294690755874547212579844885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392921007832729616773126513 294690755874547212579844885)
                  ·
                    refine ⟨13813629181619400589680229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 294690755874547212579844885 13813629181619400589680229)
                    ·
                      refine ⟨2590055471553637610565043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13813629181619400589680229 2590055471553637610565043)
                      ·
                        rfl

theorem cell23_5044115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_5044115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044115 prefixEnd_5044115 := by exact prefixLift 5044115
  have htrace : WordTrace (prefixWord ++ tailWord_5044115) baseStart_5044115 baseEnd_5044115 := by
    simpa [prefixWord, tailWord_5044115, baseEnd_5044115] using wordTrace_append hprefix tailTrace_5044115
  have hstable : (prefixWord ++ tailWord_5044115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044115).length < 2 ^ (prefixWord ++ tailWord_5044115).sum := by decide
  have hdescent : baseEnd_5044115 < baseStart_5044115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044116 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5044116 : Nat := 118140960795 + 5044116 * 2 ^ 59
def prefixEnd_5044116 : Nat := 4983230072969 + 3 ^ 40 * 5044116 * 2
def baseEnd_5044116 : Nat := 863351995011430702217513

theorem tailTrace_5044116 : CollatzResearch.WordTrace tailWord_5044116 prefixEnd_5044116 863351995011430702217513 := by
  unfold tailWord_5044116
  simp only [CollatzResearch.WordTrace]
  refine ⟨91987012297018336636532101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122649349729357782182042801 91987012297018336636532101)
  ·
    refine ⟨17247564805690938119349769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91987012297018336636532101 17247564805690938119349769)
    ·
      refine ⟨12935673604268203589512327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17247564805690938119349769 12935673604268203589512327)
      ·
        refine ⟨19403510406402305384268491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12935673604268203589512327 19403510406402305384268491)
        ·
          refine ⟨29105265609603458076402737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19403510406402305384268491 29105265609603458076402737)
          ·
            refine ⟨21828949207202593557302053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29105265609603458076402737 21828949207202593557302053)
            ·
              refine ⟨4092927976350486291994135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21828949207202593557302053 4092927976350486291994135)
              ·
                refine ⟨6139391964525729437991203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092927976350486291994135 6139391964525729437991203)
                ·
                  refine ⟨9209087946788594156986805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139391964525729437991203 9209087946788594156986805)
                  ·
                    refine ⟨863351995011430702217513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9209087946788594156986805 863351995011430702217513)
                    ·
                      rfl

theorem cell23_5044116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5044116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044116 prefixEnd_5044116 := by exact prefixLift 5044116
  have htrace : WordTrace (prefixWord ++ tailWord_5044116) baseStart_5044116 baseEnd_5044116 := by
    simpa [prefixWord, tailWord_5044116, baseEnd_5044116] using wordTrace_append hprefix tailTrace_5044116
  have hstable : (prefixWord ++ tailWord_5044116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044116).length < 2 ^ (prefixWord ++ tailWord_5044116).sum := by decide
  have hdescent : baseEnd_5044116 < baseStart_5044116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044119 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_5044119 : Nat := 118140960795 + 5044119 * 2 ^ 59
def prefixEnd_5044119 : Nat := 4983230072969 + 3 ^ 40 * 5044119 * 2
def baseEnd_5044119 : Nat := 2590057525476255594915025

theorem tailTrace_5044119 : CollatzResearch.WordTrace tailWord_5044119 prefixEnd_5044119 2590057525476255594915025 := by
  unfold tailWord_5044119
  simp only [CollatzResearch.WordTrace]
  refine ⟨183974134013025804785423411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122649422675350536523615607 183974134013025804785423411)
  ·
    refine ⟨275961201019538707178135117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183974134013025804785423411 275961201019538707178135117)
    ·
      refine ⟨103485450382327015191800669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275961201019538707178135117 103485450382327015191800669)
      ·
        refine ⟨38807043893372630696925251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103485450382327015191800669 38807043893372630696925251)
        ·
          refine ⟨58210565840058946045387877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38807043893372630696925251 58210565840058946045387877)
          ·
            refine ⟨10914481095011052383510227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58210565840058946045387877 10914481095011052383510227)
            ·
              refine ⟨16371721642516578575265341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10914481095011052383510227 16371721642516578575265341)
              ·
                refine ⟨6139395615943716965724503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16371721642516578575265341 6139395615943716965724503)
                ·
                  refine ⟨9209093423915575448586755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6139395615943716965724503 9209093423915575448586755)
                  ·
                    refine ⟨13813640135873363172880133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9209093423915575448586755 13813640135873363172880133)
                    ·
                      refine ⟨2590057525476255594915025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13813640135873363172880133 2590057525476255594915025)
                      ·
                        rfl

theorem cell23_5044119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_5044119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044119 prefixEnd_5044119 := by exact prefixLift 5044119
  have htrace : WordTrace (prefixWord ++ tailWord_5044119) baseStart_5044119 baseEnd_5044119 := by
    simpa [prefixWord, tailWord_5044119, baseEnd_5044119] using wordTrace_append hprefix tailTrace_5044119
  have hstable : (prefixWord ++ tailWord_5044119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044119).length < 2 ^ (prefixWord ++ tailWord_5044119).sum := by decide
  have hdescent : baseEnd_5044119 < baseStart_5044119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044149 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_5044149 : Nat := 118140960795 + 5044149 * 2 ^ 59
def prefixEnd_5044149 : Nat := 4983230072969 + 3 ^ 40 * 5044149 * 2
def baseEnd_5044149 : Nat := 2590072929895890477539887

theorem tailTrace_5044149 : CollatzResearch.WordTrace tailWord_5044149 prefixEnd_5044149 2590072929895890477539887 := by
  unfold tailWord_5044149
  simp only [CollatzResearch.WordTrace]
  refine ⟨183975228202917119909015501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122650152135278079939343667 183975228202917119909015501)
  ·
    refine ⟨68990710576093919965880813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183975228202917119909015501 68990710576093919965880813)
    ·
      refine ⟨25871516466035219987205305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68990710576093919965880813 25871516466035219987205305)
      ·
        refine ⟨19403637349526414990403979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25871516466035219987205305 19403637349526414990403979)
        ·
          refine ⟨29105456024289622485605969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19403637349526414990403979 29105456024289622485605969)
          ·
            refine ⟨21829092018217216864204477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29105456024289622485605969 21829092018217216864204477)
            ·
              refine ⟨8185909506831456324076679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21829092018217216864204477 8185909506831456324076679)
              ·
                refine ⟨12278864260247184486115019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8185909506831456324076679 12278864260247184486115019)
                ·
                  refine ⟨18418296390370776729172529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12278864260247184486115019 18418296390370776729172529)
                  ·
                    refine ⟨13813722292778082546879397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18418296390370776729172529 13813722292778082546879397)
                    ·
                      refine ⟨2590072929895890477539887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13813722292778082546879397 2590072929895890477539887)
                      ·
                        rfl

theorem cell23_5044149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_5044149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044149 prefixEnd_5044149 := by exact prefixLift 5044149
  have htrace : WordTrace (prefixWord ++ tailWord_5044149) baseStart_5044149 baseEnd_5044149 := by
    simpa [prefixWord, tailWord_5044149, baseEnd_5044149] using wordTrace_append hprefix tailTrace_5044149
  have hstable : (prefixWord ++ tailWord_5044149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044149).length < 2 ^ (prefixWord ++ tailWord_5044149).sum := by decide
  have hdescent : baseEnd_5044149 < baseStart_5044149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044155 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 7]
def baseStart_5044155 : Nat := 118140960795 + 5044155 * 2 ^ 59
def prefixEnd_5044155 : Nat := 4983230072969 + 3 ^ 40 * 5044155 * 2
def baseEnd_5044155 : Nat := 863358670259939151354953

theorem tailTrace_5044155 : CollatzResearch.WordTrace tailWord_5044155 prefixEnd_5044155 863358670259939151354953 := by
  unfold tailWord_5044155
  simp only [CollatzResearch.WordTrace]
  refine ⟨183975447040895382933733919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122650298027263588622489279 183975447040895382933733919)
  ·
    refine ⟨275963170561343074400600879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183975447040895382933733919 275963170561343074400600879)
    ·
      refine ⟨413944755842014611600901319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275963170561343074400600879 413944755842014611600901319)
      ·
        refine ⟨620917133763021917401351979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413944755842014611600901319 620917133763021917401351979)
        ·
          refine ⟨931375700644532876102027969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620917133763021917401351979 931375700644532876102027969)
          ·
            refine ⟨698531775483399657076520977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931375700644532876102027969 698531775483399657076520977)
            ·
              refine ⟨523898831612549742807390733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698531775483399657076520977 523898831612549742807390733)
              ·
                refine ⟨196462061854706153552771525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 523898831612549742807390733 196462061854706153552771525)
                ·
                  refine ⟨36836636597757403791144661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196462061854706153552771525 36836636597757403791144661)
                  ·
                    refine ⟨863358670259939151354953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36836636597757403791144661 863358670259939151354953)
                    ·
                      rfl

theorem cell23_5044155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_5044155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044155 prefixEnd_5044155 := by exact prefixLift 5044155
  have htrace : WordTrace (prefixWord ++ tailWord_5044155) baseStart_5044155 baseEnd_5044155 := by
    simpa [prefixWord, tailWord_5044155, baseEnd_5044155] using wordTrace_append hprefix tailTrace_5044155
  have hstable : (prefixWord ++ tailWord_5044155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044155).length < 2 ^ (prefixWord ++ tailWord_5044155).sum := by decide
  have hdescent : baseEnd_5044155 < baseStart_5044155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044202 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_5044202 : Nat := 118140960795 + 5044202 * 2 ^ 59
def prefixEnd_5044202 : Nat := 4983230072969 + 3 ^ 40 * 5044202 * 2
def baseEnd_5044202 : Nat := 863366714790192923392381

theorem tailTrace_5044202 : CollatzResearch.WordTrace tailWord_5044202 prefixEnd_5044202 863366714790192923392381 := by
  unfold tailWord_5044202
  simp only [CollatzResearch.WordTrace]
  refine ⟨45994290317931277490173715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122651440847816739973796573 45994290317931277490173715)
  ·
    refine ⟨68991435476896916235260573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45994290317931277490173715 68991435476896916235260573)
    ·
      refine ⟨25871788303836343588222715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68991435476896916235260573 25871788303836343588222715)
      ·
        refine ⟨38807682455754515382334073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25871788303836343588222715 38807682455754515382334073)
        ·
          refine ⟨29105761841815886536750555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38807682455754515382334073 29105761841815886536750555)
          ·
            refine ⟨43658642762723829805125833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29105761841815886536750555 43658642762723829805125833)
            ·
              refine ⟨32743982072042872353844375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43658642762723829805125833 32743982072042872353844375)
              ·
                refine ⟨49115973108064308530766563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32743982072042872353844375 49115973108064308530766563)
                ·
                  refine ⟨73673959662096462796149845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49115973108064308530766563 73673959662096462796149845)
                  ·
                    refine ⟨863366714790192923392381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73673959662096462796149845 863366714790192923392381)
                    ·
                      rfl

theorem cell23_5044202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_5044202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044202 prefixEnd_5044202 := by exact prefixLift 5044202
  have htrace : WordTrace (prefixWord ++ tailWord_5044202) baseStart_5044202 baseEnd_5044202 := by
    simpa [prefixWord, tailWord_5044202, baseEnd_5044202] using wordTrace_append hprefix tailTrace_5044202
  have hstable : (prefixWord ++ tailWord_5044202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044202).length < 2 ^ (prefixWord ++ tailWord_5044202).sum := by decide
  have hdescent : baseEnd_5044202 < baseStart_5044202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044259 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3]
def baseStart_5044259 : Nat := 118140960795 + 5044259 * 2 ^ 59
def prefixEnd_5044259 : Nat := 4983230072969 + 3 ^ 40 * 5044259 * 2
def baseEnd_5044259 : Nat := 2590129412767885047164381

theorem tailTrace_5044259 : CollatzResearch.WordTrace tailWord_5044259 prefixEnd_5044259 2590129412767885047164381 := by
  unfold tailWord_5044259
  simp only [CollatzResearch.WordTrace]
  refine ⟨183979240232518608695519831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122652826821679072463679887 183979240232518608695519831)
  ·
    refine ⟨275968860348777913043279747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183979240232518608695519831 275968860348777913043279747)
    ·
      refine ⟨413953290523166869564919621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275968860348777913043279747 413953290523166869564919621)
      ·
        refine ⟨77616241973093788043422429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 413953290523166869564919621 77616241973093788043422429)
        ·
          refine ⟨29106090739910170516283411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77616241973093788043422429 29106090739910170516283411)
          ·
            refine ⟨43659136109865255774425117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29106090739910170516283411 43659136109865255774425117)
            ·
              refine ⟨16372176041199470915409419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43659136109865255774425117 16372176041199470915409419)
              ·
                refine ⟨24558264061799206373114129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16372176041199470915409419 24558264061799206373114129)
                ·
                  refine ⟨18418698046349404779835597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24558264061799206373114129 18418698046349404779835597)
                  ·
                    refine ⟨6907011767381026792438349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18418698046349404779835597 6907011767381026792438349)
                    ·
                      refine ⟨2590129412767885047164381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907011767381026792438349 2590129412767885047164381)
                      ·
                        rfl

theorem cell23_5044259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_5044259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044259 prefixEnd_5044259 := by exact prefixLift 5044259
  have htrace : WordTrace (prefixWord ++ tailWord_5044259) baseStart_5044259 baseEnd_5044259 := by
    simpa [prefixWord, tailWord_5044259, baseEnd_5044259] using wordTrace_append hprefix tailTrace_5044259
  have hstable : (prefixWord ++ tailWord_5044259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044259).length < 2 ^ (prefixWord ++ tailWord_5044259).sum := by decide
  have hdescent : baseEnd_5044259 < baseStart_5044259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044279 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 2, 5]
def baseStart_5044279 : Nat := 118140960795 + 5044279 * 2 ^ 59
def prefixEnd_5044279 : Nat := 4983230072969 + 3 ^ 40 * 5044279 * 2
def baseEnd_5044279 : Nat := 863379894126991656304763

theorem tailTrace_5044279 : CollatzResearch.WordTrace tailWord_5044279 prefixEnd_5044279 863379894126991656304763 := by
  unfold tailWord_5044279
  simp only [CollatzResearch.WordTrace]
  refine ⟨183979969692446152111247891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122653313128297434740831927 183979969692446152111247891)
  ·
    refine ⟨275969954538669228166871837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183979969692446152111247891 275969954538669228166871837)
    ·
      refine ⟨103488732952000960562576939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275969954538669228166871837 103488732952000960562576939)
      ·
        refine ⟨155233099428001440843865409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103488732952000960562576939 155233099428001440843865409)
        ·
          refine ⟨116424824571001080632899057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155233099428001440843865409 116424824571001080632899057)
          ·
            refine ⟨87318618428250810474674293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116424824571001080632899057 87318618428250810474674293)
            ·
              refine ⟨8186120477648513482000715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87318618428250810474674293 8186120477648513482000715)
              ·
                refine ⟨12279180716472770223001073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186120477648513482000715 12279180716472770223001073)
                ·
                  refine ⟨9209385537354577667250805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12279180716472770223001073 9209385537354577667250805)
                  ·
                    refine ⟨863379894126991656304763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9209385537354577667250805 863379894126991656304763)
                    ·
                      rfl

theorem cell23_5044279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_5044279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044279 prefixEnd_5044279 := by exact prefixLift 5044279
  have htrace : WordTrace (prefixWord ++ tailWord_5044279) baseStart_5044279 baseEnd_5044279 := by
    simpa [prefixWord, tailWord_5044279, baseEnd_5044279] using wordTrace_append hprefix tailTrace_5044279
  have hstable : (prefixWord ++ tailWord_5044279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044279).length < 2 ^ (prefixWord ++ tailWord_5044279).sum := by decide
  have hdescent : baseEnd_5044279 < baseStart_5044279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044299 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 6, 2]
def baseStart_5044299 : Nat := 118140960795 + 5044299 * 2 ^ 59
def prefixEnd_5044299 : Nat := 4983230072969 + 3 ^ 40 * 5044299 * 2
def baseEnd_5044299 : Nat := 2590149951994064890664197

theorem tailTrace_5044299 : CollatzResearch.WordTrace tailWord_5044299 prefixEnd_5044299 2590149951994064890664197 := by
  unfold tailWord_5044299
  simp only [CollatzResearch.WordTrace]
  refine ⟨183980699152373695526975951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122653799434915797017983967 183980699152373695526975951)
  ·
    refine ⟨275971048728560543290463927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183980699152373695526975951 275971048728560543290463927)
    ·
      refine ⟨413956573092840814935695891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275971048728560543290463927 413956573092840814935695891)
      ·
        refine ⟨620934859639261222403543837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413956573092840814935695891 620934859639261222403543837)
        ·
          refine ⟨232850572364722958401328939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 620934859639261222403543837 232850572364722958401328939)
          ·
            refine ⟨349275858547084437601993409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232850572364722958401328939 349275858547084437601993409)
            ·
              refine ⟨261956893910313328201495057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349275858547084437601993409 261956893910313328201495057)
              ·
                refine ⟨196467670432734996151121293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261956893910313328201495057 196467670432734996151121293)
                ·
                  refine ⟨73675376412275623556670485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196467670432734996151121293 73675376412275623556670485)
                  ·
                    refine ⟨3453533269325419854218929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73675376412275623556670485 3453533269325419854218929)
                    ·
                      refine ⟨2590149951994064890664197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453533269325419854218929 2590149951994064890664197)
                      ·
                        rfl

theorem cell23_5044299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6, 2].length) (baseStart_5044299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044299 prefixEnd_5044299 := by exact prefixLift 5044299
  have htrace : WordTrace (prefixWord ++ tailWord_5044299) baseStart_5044299 baseEnd_5044299 := by
    simpa [prefixWord, tailWord_5044299, baseEnd_5044299] using wordTrace_append hprefix tailTrace_5044299
  have hstable : (prefixWord ++ tailWord_5044299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044299).length < 2 ^ (prefixWord ++ tailWord_5044299).sum := by decide
  have hdescent : baseEnd_5044299 < baseStart_5044299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044319 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_5044319 : Nat := 118140960795 + 5044319 * 2 ^ 59
def prefixEnd_5044319 : Nat := 4983230072969 + 3 ^ 40 * 5044319 * 2
def baseEnd_5044319 : Nat := 2590160221607154812414105

theorem tailTrace_5044319 : CollatzResearch.WordTrace tailWord_5044319 prefixEnd_5044319 2590160221607154812414105 := by
  unfold tailWord_5044319
  simp only [CollatzResearch.WordTrace]
  refine ⟨183981428612301238942704011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122654285741534159295136007 183981428612301238942704011)
  ·
    refine ⟨275972142918451858414056017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183981428612301238942704011 275972142918451858414056017)
    ·
      refine ⟨206979107188838893810542013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275972142918451858414056017 206979107188838893810542013)
      ·
        refine ⟨77617165195814585178953255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206979107188838893810542013 77617165195814585178953255)
        ·
          refine ⟨116425747793721877768429883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77617165195814585178953255 116425747793721877768429883)
          ·
            refine ⟨174638621690582816652644825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116425747793721877768429883 174638621690582816652644825)
            ·
              refine ⟨130978966267937112489483619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174638621690582816652644825 130978966267937112489483619)
              ·
                refine ⟨196468449401905668734225429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130978966267937112489483619 196468449401905668734225429)
                ·
                  refine ⟨9209458565714328221916817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196468449401905668734225429 9209458565714328221916817)
                  ·
                    refine ⟨6907093924285746166437613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9209458565714328221916817 6907093924285746166437613)
                    ·
                      refine ⟨2590160221607154812414105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907093924285746166437613 2590160221607154812414105)
                      ·
                        rfl

theorem cell23_5044319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_5044319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044319 prefixEnd_5044319 := by exact prefixLift 5044319
  have htrace : WordTrace (prefixWord ++ tailWord_5044319) baseStart_5044319 baseEnd_5044319 := by
    simpa [prefixWord, tailWord_5044319, baseEnd_5044319] using wordTrace_append hprefix tailTrace_5044319
  have hstable : (prefixWord ++ tailWord_5044319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044319).length < 2 ^ (prefixWord ++ tailWord_5044319).sum := by decide
  have hdescent : baseEnd_5044319 < baseStart_5044319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044343 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 1, 4]
def baseStart_5044343 : Nat := 118140960795 + 5044343 * 2 ^ 59
def prefixEnd_5044343 : Nat := 4983230072969 + 3 ^ 40 * 5044343 * 2
def baseEnd_5044343 : Nat := 863390848380954239504665

theorem tailTrace_5044343 : CollatzResearch.WordTrace tailWord_5044343 prefixEnd_5044343 863390848380954239504665 := by
  unfold tailWord_5044343
  simp only [CollatzResearch.WordTrace]
  refine ⟨183982303964214291041577683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122654869309476194027718455 183982303964214291041577683)
  ·
    refine ⟨275973455946321436562366525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183982303964214291041577683 275973455946321436562366525)
    ·
      refine ⟨103490045979870538710887447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275973455946321436562366525 103490045979870538710887447)
      ·
        refine ⟨155235068969805808066331171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103490045979870538710887447 155235068969805808066331171)
        ·
          refine ⟨232852603454708712099496757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155235068969805808066331171 232852603454708712099496757)
          ·
            refine ⟨21829931573878941759327821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232852603454708712099496757 21829931573878941759327821)
            ·
              refine ⟨8186224340204603159747933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21829931573878941759327821 8186224340204603159747933)
              ·
                refine ⟨3069834127576726184905475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8186224340204603159747933 3069834127576726184905475)
                ·
                  refine ⟨4604751191365089277358213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069834127576726184905475 4604751191365089277358213)
                  ·
                    refine ⟨863390848380954239504665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4604751191365089277358213 863390848380954239504665)
                    ·
                      rfl

theorem cell23_5044343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_5044343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044343 prefixEnd_5044343 := by exact prefixLift 5044343
  have htrace : WordTrace (prefixWord ++ tailWord_5044343) baseStart_5044343 baseEnd_5044343 := by
    simpa [prefixWord, tailWord_5044343, baseEnd_5044343] using wordTrace_append hprefix tailTrace_5044343
  have hstable : (prefixWord ++ tailWord_5044343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044343).length < 2 ^ (prefixWord ++ tailWord_5044343).sum := by decide
  have hdescent : baseEnd_5044343 < baseStart_5044343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044353 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_5044353 : Nat := 118140960795 + 5044353 * 2 ^ 59
def prefixEnd_5044353 : Nat := 4983230072969 + 3 ^ 40 * 5044353 * 2
def baseEnd_5044353 : Nat := 2590177679949407679388949

theorem tailTrace_5044353 : CollatzResearch.WordTrace tailWord_5044353 prefixEnd_5044353 2590177679949407679388949 := by
  unfold tailWord_5044353
  simp only [CollatzResearch.WordTrace]
  refine ⟨183982668694178062749441713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122655112462785375166294475 183982668694178062749441713)
  ·
    refine ⟨137987001520633547062081285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183982668694178062749441713 137987001520633547062081285)
    ·
      refine ⟨25872562785118790074140241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137987001520633547062081285 25872562785118790074140241)
      ·
        refine ⟨19404422088839092555605181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25872562785118790074140241 19404422088839092555605181)
        ·
          refine ⟨7276658283314659708351943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19404422088839092555605181 7276658283314659708351943)
          ·
            refine ⟨10914987424971989562527915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7276658283314659708351943 10914987424971989562527915)
            ·
              refine ⟨16372481137457984343791873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10914987424971989562527915 16372481137457984343791873)
              ·
                refine ⟨12279360853093488257843905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16372481137457984343791873 12279360853093488257843905)
                ·
                  refine ⟨9209520639820116193382929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12279360853093488257843905 9209520639820116193382929)
                  ·
                    refine ⟨6907140479865087145037197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9209520639820116193382929 6907140479865087145037197)
                    ·
                      refine ⟨2590177679949407679388949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907140479865087145037197 2590177679949407679388949)
                      ·
                        rfl

theorem cell23_5044353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_5044353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044353 prefixEnd_5044353 := by exact prefixLift 5044353
  have htrace : WordTrace (prefixWord ++ tailWord_5044353) baseStart_5044353 baseEnd_5044353 := by
    simpa [prefixWord, tailWord_5044353, baseEnd_5044353] using wordTrace_append hprefix tailTrace_5044353
  have hstable : (prefixWord ++ tailWord_5044353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044353).length < 2 ^ (prefixWord ++ tailWord_5044353).sum := by decide
  have hdescent : baseEnd_5044353 < baseStart_5044353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044426 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_5044426 : Nat := 118140960795 + 5044426 * 2 ^ 59
def prefixEnd_5044426 : Nat := 4983230072969 + 3 ^ 40 * 5044426 * 2
def baseEnd_5044426 : Nat := 2590215164037185893776113

theorem tailTrace_5044426 : CollatzResearch.WordTrace tailWord_5044426 prefixEnd_5044426 2590215164037185893776113 := by
  unfold tailWord_5044426
  simp only [CollatzResearch.WordTrace]
  refine ⟨45996332805728399054212283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122656887481942397477899421 45996332805728399054212283)
  ·
    refine ⟨68994499208592598581318425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45996332805728399054212283 68994499208592598581318425)
    ·
      refine ⟨51745874406444448935988819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68994499208592598581318425 51745874406444448935988819)
      ·
        refine ⟨77618811609666673403983229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51745874406444448935988819 77618811609666673403983229)
        ·
          refine ⟨29107054353625002526493711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77618811609666673403983229 29107054353625002526493711)
          ·
            refine ⟨43660581530437503789740567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29107054353625002526493711 43660581530437503789740567)
            ·
              refine ⟨65490872295656255684610851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43660581530437503789740567 65490872295656255684610851)
              ·
                refine ⟨98236308443484383526916277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65490872295656255684610851 98236308443484383526916277)
                ·
                  refine ⟨9209653916576660955648401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98236308443484383526916277 9209653916576660955648401)
                  ·
                    refine ⟨6907240437432495716736301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9209653916576660955648401 6907240437432495716736301)
                    ·
                      refine ⟨2590215164037185893776113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907240437432495716736301 2590215164037185893776113)
                      ·
                        rfl

theorem cell23_5044426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_5044426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044426 prefixEnd_5044426 := by exact prefixLift 5044426
  have htrace : WordTrace (prefixWord ++ tailWord_5044426) baseStart_5044426 baseEnd_5044426 := by
    simpa [prefixWord, tailWord_5044426, baseEnd_5044426] using wordTrace_append hprefix tailTrace_5044426
  have hstable : (prefixWord ++ tailWord_5044426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044426).length < 2 ^ (prefixWord ++ tailWord_5044426).sum := by decide
  have hdescent : baseEnd_5044426 < baseStart_5044426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044440 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_5044440 : Nat := 118140960795 + 5044440 * 2 ^ 59
def prefixEnd_5044440 : Nat := 4983230072969 + 3 ^ 40 * 5044440 * 2
def baseEnd_5044440 : Nat := 2590222352766348839001049

theorem tailTrace_5044440 : CollatzResearch.WordTrace tailWord_5044440 prefixEnd_5044440 2590222352766348839001049 := by
  unfold tailWord_5044440
  simp only [CollatzResearch.WordTrace]
  refine ⟨91992920922431438303929387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122657227896575251071905849 91992920922431438303929387)
  ·
    refine ⟨137989381383647157455894081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91992920922431438303929387 137989381383647157455894081)
    ·
      refine ⟨103492036037735368091920561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137989381383647157455894081 103492036037735368091920561)
      ·
        refine ⟨77619027028301526068940421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103492036037735368091920561 77619027028301526068940421)
        ·
          refine ⟨14553567567806536137926329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77619027028301526068940421 14553567567806536137926329)
          ·
            refine ⟨10915175675854902103444747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14553567567806536137926329 10915175675854902103444747)
            ·
              refine ⟨16372763513782353155167121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10915175675854902103444747 16372763513782353155167121)
              ·
                refine ⟨12279572635336764866375341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16372763513782353155167121 12279572635336764866375341)
                ·
                  refine ⟨4604839738251286824890753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12279572635336764866375341 4604839738251286824890753)
                  ·
                    refine ⟨3453629803688465118668065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604839738251286824890753 3453629803688465118668065)
                    ·
                      refine ⟨2590222352766348839001049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453629803688465118668065 2590222352766348839001049)
                      ·
                        rfl

theorem cell23_5044440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_5044440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044440 prefixEnd_5044440 := by exact prefixLift 5044440
  have htrace : WordTrace (prefixWord ++ tailWord_5044440) baseStart_5044440 baseEnd_5044440 := by
    simpa [prefixWord, tailWord_5044440, baseEnd_5044440] using wordTrace_append hprefix tailTrace_5044440
  have hstable : (prefixWord ++ tailWord_5044440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044440).length < 2 ^ (prefixWord ++ tailWord_5044440).sum := by decide
  have hdescent : baseEnd_5044440 < baseStart_5044440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044444 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5044444 : Nat := 118140960795 + 5044444 * 2 ^ 59
def prefixEnd_5044444 : Nat := 4983230072969 + 3 ^ 40 * 5044444 * 2
def baseEnd_5044444 : Nat := 2590224406688966823351031

theorem tailTrace_5044444 : CollatzResearch.WordTrace tailWord_5044444 prefixEnd_5044444 2590224406688966823351031 := by
  unfold tailWord_5044444
  simp only [CollatzResearch.WordTrace]
  refine ⟨91992993868424192645502193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122657325157898923527336257 91992993868424192645502193)
  ·
    refine ⟨68994745401318144484126645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91992993868424192645502193 68994745401318144484126645)
    ·
      refine ⟨6468257381373576045386873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68994745401318144484126645 6468257381373576045386873)
      ·
        refine ⟨4851193036030182034040155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6468257381373576045386873 4851193036030182034040155)
        ·
          refine ⟨7276789554045273051060233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851193036030182034040155 7276789554045273051060233)
          ·
            refine ⟨5457592165533954788295175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7276789554045273051060233 5457592165533954788295175)
            ·
              refine ⟨8186388248300932182442763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457592165533954788295175 8186388248300932182442763)
              ·
                refine ⟨12279582372451398273664145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186388248300932182442763 12279582372451398273664145)
                ·
                  refine ⟨9209686779338548705248109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12279582372451398273664145 9209686779338548705248109)
                  ·
                    refine ⟨3453632542251955764468041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9209686779338548705248109 3453632542251955764468041)
                    ·
                      refine ⟨2590224406688966823351031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453632542251955764468041 2590224406688966823351031)
                      ·
                        rfl

theorem cell23_5044444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5044444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044444 prefixEnd_5044444 := by exact prefixLift 5044444
  have htrace : WordTrace (prefixWord ++ tailWord_5044444) baseStart_5044444 baseEnd_5044444 := by
    simpa [prefixWord, tailWord_5044444, baseEnd_5044444] using wordTrace_append hprefix tailTrace_5044444
  have hstable : (prefixWord ++ tailWord_5044444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044444).length < 2 ^ (prefixWord ++ tailWord_5044444).sum := by decide
  have hdescent : baseEnd_5044444 < baseStart_5044444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044473 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 3]
def baseStart_5044473 : Nat := 118140960795 + 5044473 * 2 ^ 59
def prefixEnd_5044473 : Nat := 4983230072969 + 3 ^ 40 * 5044473 * 2
def baseEnd_5044473 : Nat := 2590239297627947209888397

theorem tailTrace_5044473 : CollatzResearch.WordTrace tailWord_5044473 prefixEnd_5044473 2590239297627947209888397 := by
  unfold tailWord_5044473
  simp only [CollatzResearch.WordTrace]
  refine ⟨183987045453743323243810073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122658030302495548829206715 183987045453743323243810073)
  ·
    refine ⟨137990284090307492432857555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183987045453743323243810073 137990284090307492432857555)
    ·
      refine ⟨206985426135461238649286333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137990284090307492432857555 206985426135461238649286333)
      ·
        refine ⟨77619534800797964493482375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206985426135461238649286333 77619534800797964493482375)
        ·
          refine ⟨116429302201196946740223563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77619534800797964493482375 116429302201196946740223563)
          ·
            refine ⟨174643953301795420110335345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116429302201196946740223563 174643953301795420110335345)
            ·
              refine ⟨130982964976346565082751509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174643953301795420110335345 130982964976346565082751509)
              ·
                refine ⟨6139826483266245238253977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130982964976346565082751509 6139826483266245238253977)
                ·
                  refine ⟨4604869862449683928690483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6139826483266245238253977 4604869862449683928690483)
                  ·
                    refine ⟨6907304793674525893035725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4604869862449683928690483 6907304793674525893035725)
                    ·
                      refine ⟨2590239297627947209888397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907304793674525893035725 2590239297627947209888397)
                      ·
                        rfl

theorem cell23_5044473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_5044473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044473 prefixEnd_5044473 := by exact prefixLift 5044473
  have htrace : WordTrace (prefixWord ++ tailWord_5044473) baseStart_5044473 baseEnd_5044473 := by
    simpa [prefixWord, tailWord_5044473, baseEnd_5044473] using wordTrace_append hprefix tailTrace_5044473
  have hstable : (prefixWord ++ tailWord_5044473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044473).length < 2 ^ (prefixWord ++ tailWord_5044473).sum := by decide
  have hdescent : baseEnd_5044473 < baseStart_5044473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044487 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5044487 : Nat := 118140960795 + 5044487 * 2 ^ 59
def prefixEnd_5044487 : Nat := 4983230072969 + 3 ^ 40 * 5044487 * 2
def baseEnd_5044487 : Nat := 2590246486357110155113333

theorem tailTrace_5044487 : CollatzResearch.WordTrace tailWord_5044487 prefixEnd_5044487 2590246486357110155113333 := by
  unfold tailWord_5044487
  simp only [CollatzResearch.WordTrace]
  refine ⟨183987556075692603634819715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122658370717128402423213143 183987556075692603634819715)
  ·
    refine ⟨275981334113538905452229573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183987556075692603634819715 275981334113538905452229573)
    ·
      refine ⟨51746500146288544772293045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275981334113538905452229573 51746500146288544772293045)
      ·
        refine ⟨4851234388714551072402473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51746500146288544772293045 4851234388714551072402473)
        ·
          refine ⟨3638425791535913304301855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4851234388714551072402473 3638425791535913304301855)
          ·
            refine ⟨5457638687303869956452783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638425791535913304301855 5457638687303869956452783)
            ·
              refine ⟨8186458030955804934679175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457638687303869956452783 8186458030955804934679175)
              ·
                refine ⟨12279687046433707402018763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186458030955804934679175 12279687046433707402018763)
                ·
                  refine ⟨18419530569650561103028145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12279687046433707402018763 18419530569650561103028145)
                  ·
                    refine ⟨13814647927237920827271109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18419530569650561103028145 13814647927237920827271109)
                    ·
                      refine ⟨2590246486357110155113333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13814647927237920827271109 2590246486357110155113333)
                      ·
                        rfl

theorem cell23_5044487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5044487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044487 prefixEnd_5044487 := by exact prefixLift 5044487
  have htrace : WordTrace (prefixWord ++ tailWord_5044487) baseStart_5044487 baseEnd_5044487 := by
    simpa [prefixWord, tailWord_5044487, baseEnd_5044487] using wordTrace_append hprefix tailTrace_5044487
  have hstable : (prefixWord ++ tailWord_5044487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044487).length < 2 ^ (prefixWord ++ tailWord_5044487).sum := by decide
  have hdescent : baseEnd_5044487 < baseStart_5044487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044499 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_5044499 : Nat := 118140960795 + 5044499 * 2 ^ 59
def prefixEnd_5044499 : Nat := 4983230072969 + 3 ^ 40 * 5044499 * 2
def baseEnd_5044499 : Nat := 2590252648124964108163277

theorem tailTrace_5044499 : CollatzResearch.WordTrace tailWord_5044499 prefixEnd_5044499 2590252648124964108163277 := by
  unfold tailWord_5044499
  simp only [CollatzResearch.WordTrace]
  refine ⟨183987993751649129684256551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122658662501099419789504367 183987993751649129684256551)
  ·
    refine ⟨275981990627473694526384827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183987993751649129684256551 275981990627473694526384827)
    ·
      refine ⟨413972985941210541789577241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275981990627473694526384827 413972985941210541789577241)
      ·
        refine ⟨310479739455907906342182931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413972985941210541789577241 310479739455907906342182931)
        ·
          refine ⟨465719609183861859513274397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310479739455907906342182931 465719609183861859513274397)
          ·
            refine ⟨174644853443948197317477899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465719609183861859513274397 174644853443948197317477899)
            ·
              refine ⟨261967280165922295976216849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174644853443948197317477899 261967280165922295976216849)
              ·
                refine ⟨196475460124441721982162637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261967280165922295976216849 196475460124441721982162637)
                ·
                  refine ⟨73678297546665645743310989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196475460124441721982162637 73678297546665645743310989)
                  ·
                    refine ⟨27629361579999617153741621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73678297546665645743310989 27629361579999617153741621)
                    ·
                      refine ⟨2590252648124964108163277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27629361579999617153741621 2590252648124964108163277)
                      ·
                        rfl

theorem cell23_5044499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_5044499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044499 prefixEnd_5044499 := by exact prefixLift 5044499
  have htrace : WordTrace (prefixWord ++ tailWord_5044499) baseStart_5044499 baseEnd_5044499 := by
    simpa [prefixWord, tailWord_5044499, baseEnd_5044499] using wordTrace_append hprefix tailTrace_5044499
  have hstable : (prefixWord ++ tailWord_5044499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044499).length < 2 ^ (prefixWord ++ tailWord_5044499).sum := by decide
  have hdescent : baseEnd_5044499 < baseStart_5044499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044513 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5044513 : Nat := 118140960795 + 5044513 * 2 ^ 59
def prefixEnd_5044513 : Nat := 4983230072969 + 3 ^ 40 * 5044513 * 2
def baseEnd_5044513 : Nat := 2590259836854127053388213

theorem tailTrace_5044513 : CollatzResearch.WordTrace tailWord_5044513 prefixEnd_5044513 2590259836854127053388213 := by
  unfold tailWord_5044513
  simp only [CollatzResearch.WordTrace]
  refine ⟨183988504373598410075266193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122659002915732273383510795 183988504373598410075266193)
  ·
    refine ⟨137991378280198807556449645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183988504373598410075266193 137991378280198807556449645)
    ·
      refine ⟨51746766855074552833668617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137991378280198807556449645 51746766855074552833668617)
      ·
        refine ⟨38810075141305914625251463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51746766855074552833668617 38810075141305914625251463)
        ·
          refine ⟨58215112711958871937877195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38810075141305914625251463 58215112711958871937877195)
          ·
            refine ⟨87322669067938307906815793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58215112711958871937877195 87322669067938307906815793)
            ·
              refine ⟨65492001800953730930111845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87322669067938307906815793 65492001800953730930111845)
              ·
                refine ⟨12279750337678824549395971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65492001800953730930111845 12279750337678824549395971)
                ·
                  refine ⟨18419625506518236824093957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12279750337678824549395971 18419625506518236824093957)
                  ·
                    refine ⟨3453679782472169404517617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18419625506518236824093957 3453679782472169404517617)
                    ·
                      refine ⟨2590259836854127053388213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453679782472169404517617 2590259836854127053388213)
                      ·
                        rfl

theorem cell23_5044513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5044513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044513 prefixEnd_5044513 := by exact prefixLift 5044513
  have htrace : WordTrace (prefixWord ++ tailWord_5044513) baseStart_5044513 baseEnd_5044513 := by
    simpa [prefixWord, tailWord_5044513, baseEnd_5044513] using wordTrace_append hprefix tailTrace_5044513
  have hstable : (prefixWord ++ tailWord_5044513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044513).length < 2 ^ (prefixWord ++ tailWord_5044513).sum := by decide
  have hdescent : baseEnd_5044513 < baseStart_5044513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044516 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5044516 : Nat := 118140960795 + 5044516 * 2 ^ 59
def prefixEnd_5044516 : Nat := 4983230072969 + 3 ^ 40 * 5044516 * 2
def baseEnd_5044516 : Nat := 2590261377296090541650699

theorem tailTrace_5044516 : CollatzResearch.WordTrace tailWord_5044516 prefixEnd_5044516 2590261377296090541650699 := by
  unfold tailWord_5044516
  simp only [CollatzResearch.WordTrace]
  refine ⟨91994306896293770793812701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122659075861725027725083601 91994306896293770793812701)
  ·
    refine ⟨34497865086110164047679763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91994306896293770793812701 34497865086110164047679763)
    ·
      refine ⟨51746797629165246071519645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34497865086110164047679763 51746797629165246071519645)
      ·
        refine ⟨19405049110936967276819867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51746797629165246071519645 19405049110936967276819867)
        ·
          refine ⟨29107573666405450915229801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19405049110936967276819867 29107573666405450915229801)
          ·
            refine ⟨21830680249804088186422351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29107573666405450915229801 21830680249804088186422351)
            ·
              refine ⟨32746020374706132279633527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21830680249804088186422351 32746020374706132279633527)
              ·
                refine ⟨49119030562059198419450291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32746020374706132279633527 49119030562059198419450291)
                ·
                  refine ⟨73678545843088797629175437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49119030562059198419450291 73678545843088797629175437)
                  ·
                    refine ⟨27629454691158299110940789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73678545843088797629175437 27629454691158299110940789)
                    ·
                      refine ⟨2590261377296090541650699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27629454691158299110940789 2590261377296090541650699)
                      ·
                        rfl

theorem cell23_5044516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5044516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044516 prefixEnd_5044516 := by exact prefixLift 5044516
  have htrace : WordTrace (prefixWord ++ tailWord_5044516) baseStart_5044516 baseEnd_5044516 := by
    simpa [prefixWord, tailWord_5044516, baseEnd_5044516] using wordTrace_append hprefix tailTrace_5044516
  have hstable : (prefixWord ++ tailWord_5044516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044516).length < 2 ^ (prefixWord ++ tailWord_5044516).sum := by decide
  have hdescent : baseEnd_5044516 < baseStart_5044516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044536 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 7]
def baseStart_5044536 : Nat := 118140960795 + 5044536 * 2 ^ 59
def prefixEnd_5044536 : Nat := 4983230072969 + 3 ^ 40 * 5044536 * 2
def baseEnd_5044536 : Nat := 287807960767686718155623

theorem tailTrace_5044536 : CollatzResearch.WordTrace tailWord_5044536 prefixEnd_5044536 287807960767686718155623 := by
  unfold tailWord_5044536
  simp only [CollatzResearch.WordTrace]
  refine ⟨91994671626257542501676731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122659562168343390002235641 91994671626257542501676731)
  ·
    refine ⟨137992007439386313752515097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91994671626257542501676731 137992007439386313752515097)
    ·
      refine ⟨103494005579539735314386323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137992007439386313752515097 103494005579539735314386323)
      ·
        refine ⟨155241008369309602971579485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103494005579539735314386323 155241008369309602971579485)
        ·
          refine ⟨58215378138491101114342307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155241008369309602971579485 58215378138491101114342307)
          ·
            refine ⟨87323067207736651671513461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58215378138491101114342307 87323067207736651671513461)
            ·
              refine ⟨8186537550725311094204387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87323067207736651671513461 8186537550725311094204387)
              ·
                refine ⟨12279806326087966641306581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186537550725311094204387 12279806326087966641306581)
                ·
                  refine ⟨287807960767686718155623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12279806326087966641306581 287807960767686718155623)
                  ·
                    rfl

theorem cell23_5044536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_5044536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044536 prefixEnd_5044536 := by exact prefixLift 5044536
  have htrace : WordTrace (prefixWord ++ tailWord_5044536) baseStart_5044536 baseEnd_5044536 := by
    simpa [prefixWord, tailWord_5044536, baseEnd_5044536] using wordTrace_append hprefix tailTrace_5044536
  have hstable : (prefixWord ++ tailWord_5044536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044536).length < 2 ^ (prefixWord ++ tailWord_5044536).sum := by decide
  have hdescent : baseEnd_5044536 < baseStart_5044536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044547 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 2, 2, 2]
def baseStart_5044547 : Nat := 118140960795 + 5044547 * 2 ^ 59
def prefixEnd_5044547 : Nat := 4983230072969 + 3 ^ 40 * 5044547 * 2
def baseEnd_5044547 : Nat := 2590277295196379920363057

theorem tailTrace_5044547 : CollatzResearch.WordTrace tailWord_5044547 prefixEnd_5044547 2590277295196379920363057 := by
  unfold tailWord_5044547
  simp only [CollatzResearch.WordTrace]
  refine ⟨183989744455475233882003895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122659829636983489254669263 183989744455475233882003895)
  ·
    refine ⟨275984616683212850823005843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183989744455475233882003895 275984616683212850823005843)
    ·
      refine ⟨413976925024819276234508765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275984616683212850823005843 413976925024819276234508765)
      ·
        refine ⟨155241346884307228587940787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413976925024819276234508765 155241346884307228587940787)
        ·
          refine ⟨232862020326460842881911181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155241346884307228587940787 232862020326460842881911181)
          ·
            refine ⟨87323257622422816080716693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232862020326460842881911181 87323257622422816080716693)
            ·
              refine ⟨4093277701051069503783595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87323257622422816080716693 4093277701051069503783595)
              ·
                refine ⟨6139916551576604255675393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093277701051069503783595 6139916551576604255675393)
                ·
                  refine ⟨4604937413682453191756545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6139916551576604255675393 4604937413682453191756545)
                  ·
                    refine ⟨3453703060261839893817409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4604937413682453191756545 3453703060261839893817409)
                    ·
                      refine ⟨2590277295196379920363057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453703060261839893817409 2590277295196379920363057)
                      ·
                        rfl

theorem cell23_5044547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_5044547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044547 prefixEnd_5044547 := by exact prefixLift 5044547
  have htrace : WordTrace (prefixWord ++ tailWord_5044547) baseStart_5044547 baseEnd_5044547 := by
    simpa [prefixWord, tailWord_5044547, baseEnd_5044547] using wordTrace_append hprefix tailTrace_5044547
  have hstable : (prefixWord ++ tailWord_5044547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044547).length < 2 ^ (prefixWord ++ tailWord_5044547).sum := by decide
  have hdescent : baseEnd_5044547 < baseStart_5044547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044583 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5044583 : Nat := 118140960795 + 5044583 * 2 ^ 59
def prefixEnd_5044583 : Nat := 4983230072969 + 3 ^ 40 * 5044583 * 2
def baseEnd_5044583 : Nat := 863431926833313926504297

theorem tailTrace_5044583 : CollatzResearch.WordTrace tailWord_5044583 prefixEnd_5044583 863431926833313926504297 := by
  unfold tailWord_5044583
  simp only [CollatzResearch.WordTrace]
  refine ⟨183991057483344812030314403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122660704988896541353542935 183991057483344812030314403)
  ·
    refine ⟨275986586225017218045471605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183991057483344812030314403 275986586225017218045471605)
    ·
      refine ⟨25873742458595364191762963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275986586225017218045471605 25873742458595364191762963)
      ·
        refine ⟨38810613687893046287644445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25873742458595364191762963 38810613687893046287644445)
        ·
          refine ⟨14553980132959892357866667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38810613687893046287644445 14553980132959892357866667)
          ·
            refine ⟨21830970199439838536800001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14553980132959892357866667 21830970199439838536800001)
            ·
              refine ⟨16373227649579878902600001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21830970199439838536800001 16373227649579878902600001)
              ·
                refine ⟨12279920737184909176950001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16373227649579878902600001 12279920737184909176950001)
                ·
                  refine ⟨9209940552888681882712501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12279920737184909176950001 9209940552888681882712501)
                  ·
                    refine ⟨863431926833313926504297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9209940552888681882712501 863431926833313926504297)
                    ·
                      rfl

theorem cell23_5044583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5044583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044583 prefixEnd_5044583 := by exact prefixLift 5044583
  have htrace : WordTrace (prefixWord ++ tailWord_5044583) baseStart_5044583 baseEnd_5044583 := by
    simpa [prefixWord, tailWord_5044583, baseEnd_5044583] using wordTrace_append hprefix tailTrace_5044583
  have hstable : (prefixWord ++ tailWord_5044583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044583).length < 2 ^ (prefixWord ++ tailWord_5044583).sum := by decide
  have hdescent : baseEnd_5044583 < baseStart_5044583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044603 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 6, 2]
def baseStart_5044603 : Nat := 118140960795 + 5044603 * 2 ^ 59
def prefixEnd_5044603 : Nat := 4983230072969 + 3 ^ 40 * 5044603 * 2
def baseEnd_5044603 : Nat := 2590306050113031701262799

theorem tailTrace_5044603 : CollatzResearch.WordTrace tailWord_5044603 prefixEnd_5044603 2590306050113031701262799 := by
  unfold tailWord_5044603
  simp only [CollatzResearch.WordTrace]
  refine ⟨183991786943272355446042463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122661191295514903630694975 183991786943272355446042463)
  ·
    refine ⟨275987680414908533169063695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183991786943272355446042463 275987680414908533169063695)
    ·
      refine ⟨413981520622362799753595543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275987680414908533169063695 413981520622362799753595543)
      ·
        refine ⟨620972280933544199630393315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413981520622362799753595543 620972280933544199630393315)
        ·
          refine ⟨931458421400316299445589973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620972280933544199630393315 931458421400316299445589973)
          ·
            refine ⟨21831056751569913268256015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 931458421400316299445589973 21831056751569913268256015)
            ·
              refine ⟨32746585127354869902384023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21831056751569913268256015 32746585127354869902384023)
              ·
                refine ⟨49119877691032304853576035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32746585127354869902384023 49119877691032304853576035)
                ·
                  refine ⟨73679816536548457280364053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49119877691032304853576035 73679816536548457280364053)
                  ·
                    refine ⟨3453741400150708935017065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73679816536548457280364053 3453741400150708935017065)
                    ·
                      refine ⟨2590306050113031701262799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453741400150708935017065 2590306050113031701262799)
                      ·
                        rfl

theorem cell23_5044603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6, 2].length) (baseStart_5044603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044603 prefixEnd_5044603 := by exact prefixLift 5044603
  have htrace : WordTrace (prefixWord ++ tailWord_5044603) baseStart_5044603 baseEnd_5044603 := by
    simpa [prefixWord, tailWord_5044603, baseEnd_5044603] using wordTrace_append hprefix tailTrace_5044603
  have hstable : (prefixWord ++ tailWord_5044603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044603).length < 2 ^ (prefixWord ++ tailWord_5044603).sum := by decide
  have hdescent : baseEnd_5044603 < baseStart_5044603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044620 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_5044620 : Nat := 118140960795 + 5044620 * 2 ^ 59
def prefixEnd_5044620 : Nat := 4983230072969 + 3 ^ 40 * 5044620 * 2
def baseEnd_5044620 : Nat := 2590314779284158134750221

theorem tailTrace_5044620 : CollatzResearch.WordTrace tailWord_5044620 prefixEnd_5044620 2590314779284158134750221 := by
  unfold tailWord_5044620
  simp only [CollatzResearch.WordTrace]
  refine ⟨91996203492105383674705657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122661604656140511566274209 91996203492105383674705657)
  ·
    refine ⟨68997152619079037756029243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91996203492105383674705657 68997152619079037756029243)
    ·
      refine ⟨103495728928618556634043865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68997152619079037756029243 103495728928618556634043865)
      ·
        refine ⟨77621796696463917475532899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103495728928618556634043865 77621796696463917475532899)
        ·
          refine ⟨116432695044695876213299349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77621796696463917475532899 116432695044695876213299349)
          ·
            refine ⟨5457782580220119197498407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116432695044695876213299349 5457782580220119197498407)
            ·
              refine ⟨8186673870330178796247611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5457782580220119197498407 8186673870330178796247611)
              ·
                refine ⟨12280010805495268194371417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8186673870330178796247611 12280010805495268194371417)
                ·
                  refine ⟨9210008104121451145778563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12280010805495268194371417 9210008104121451145778563)
                  ·
                    refine ⟨13815012156182176718667845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9210008104121451145778563 13815012156182176718667845)
                    ·
                      refine ⟨2590314779284158134750221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13815012156182176718667845 2590314779284158134750221)
                      ·
                        rfl

theorem cell23_5044620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_5044620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044620 prefixEnd_5044620 := by exact prefixLift 5044620
  have htrace : WordTrace (prefixWord ++ tailWord_5044620) baseStart_5044620 baseEnd_5044620 := by
    simpa [prefixWord, tailWord_5044620, baseEnd_5044620] using wordTrace_append hprefix tailTrace_5044620
  have hstable : (prefixWord ++ tailWord_5044620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044620).length < 2 ^ (prefixWord ++ tailWord_5044620).sum := by decide
  have hdescent : baseEnd_5044620 < baseStart_5044620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044643 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 6]
def baseStart_5044643 : Nat := 118140960795 + 5044643 * 2 ^ 59
def prefixEnd_5044643 : Nat := 4983230072969 + 3 ^ 40 * 5044643 * 2
def baseEnd_5044643 : Nat := 287814065482134616084735

theorem tailTrace_5044643 : CollatzResearch.WordTrace tailWord_5044643 prefixEnd_5044643 287814065482134616084735 := by
  unfold tailWord_5044643
  simp only [CollatzResearch.WordTrace]
  refine ⟨183993245863127442277498583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122662163908751628184999055 183993245863127442277498583)
  ·
    refine ⟨275989868794691163416247875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183993245863127442277498583 275989868794691163416247875)
    ·
      refine ⟨413984803192036745124371813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275989868794691163416247875 413984803192036745124371813)
      ·
        refine ⟨77622150598506889710819715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 413984803192036745124371813 77622150598506889710819715)
        ·
          refine ⟨116433225897760334566229573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77622150598506889710819715 116433225897760334566229573)
          ·
            refine ⟨21831229855830062731168045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116433225897760334566229573 21831229855830062731168045)
            ·
              refine ⟨8186711195936273524188017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21831229855830062731168045 8186711195936273524188017)
              ·
                refine ⟨6140033396952205143141013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8186711195936273524188017 6140033396952205143141013)
                ·
                  refine ⟨287814065482134616084735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6140033396952205143141013 287814065482134616084735)
                  ·
                    rfl

theorem cell23_5044643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 6].length) (baseStart_5044643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044643 prefixEnd_5044643 := by exact prefixLift 5044643
  have htrace : WordTrace (prefixWord ++ tailWord_5044643) baseStart_5044643 baseEnd_5044643 := by
    simpa [prefixWord, tailWord_5044643, baseEnd_5044643] using wordTrace_append hprefix tailTrace_5044643
  have hstable : (prefixWord ++ tailWord_5044643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044643).length < 2 ^ (prefixWord ++ tailWord_5044643).sum := by decide
  have hdescent : baseEnd_5044643 < baseStart_5044643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044647 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 1, 4]
def baseStart_5044647 : Nat := 118140960795 + 5044647 * 2 ^ 59
def prefixEnd_5044647 : Nat := 4983230072969 + 3 ^ 40 * 5044647 * 2
def baseEnd_5044647 : Nat := 863442881087276509704199

theorem tailTrace_5044647 : CollatzResearch.WordTrace tailWord_5044647 prefixEnd_5044647 863442881087276509704199 := by
  unfold tailWord_5044647
  simp only [CollatzResearch.WordTrace]
  refine ⟨183993391755112950960644195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122662261170075300640429463 183993391755112950960644195)
  ·
    refine ⟨275990087632669426440966293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183993391755112950960644195 275990087632669426440966293)
    ·
      refine ⟨12937035357781379364420295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 275990087632669426440966293 12937035357781379364420295)
      ·
        refine ⟨19405553036672069046630443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12937035357781379364420295 19405553036672069046630443)
        ·
          refine ⟨29108329555008103569945665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19405553036672069046630443 29108329555008103569945665)
          ·
            refine ⟨21831247166256077677459249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29108329555008103569945665 21831247166256077677459249)
            ·
              refine ⟨16373435374692058258094437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21831247166256077677459249 16373435374692058258094437)
              ·
                refine ⟨3070019132754760923392707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16373435374692058258094437 3070019132754760923392707)
                ·
                  refine ⟨4605028699132141385089061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070019132754760923392707 4605028699132141385089061)
                  ·
                    refine ⟨863442881087276509704199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4605028699132141385089061 863442881087276509704199)
                    ·
                      rfl

theorem cell23_5044647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_5044647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044647 prefixEnd_5044647 := by exact prefixLift 5044647
  have htrace : WordTrace (prefixWord ++ tailWord_5044647) baseStart_5044647 baseEnd_5044647 := by
    simpa [prefixWord, tailWord_5044647, baseEnd_5044647] using wordTrace_append hprefix tailTrace_5044647
  have hstable : (prefixWord ++ tailWord_5044647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044647).length < 2 ^ (prefixWord ++ tailWord_5044647).sum := by decide
  have hdescent : baseEnd_5044647 < baseStart_5044647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044666 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_5044666 : Nat := 118140960795 + 5044666 * 2 ^ 59
def prefixEnd_5044666 : Nat := 4983230072969 + 3 ^ 40 * 5044666 * 2
def baseEnd_5044666 : Nat := 2590338399394264954775009

theorem tailTrace_5044666 : CollatzResearch.WordTrace tailWord_5044666 prefixEnd_5044666 2590338399394264954775009 := by
  unfold tailWord_5044666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45998521185511029301396463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122662723161362744803723901 45998521185511029301396463)
  ·
    refine ⟨68997781778266543952094695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45998521185511029301396463 68997781778266543952094695)
    ·
      refine ⟨103496672667399815928142043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68997781778266543952094695 103496672667399815928142043)
      ·
        refine ⟨155245009001099723892213065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103496672667399815928142043 155245009001099723892213065)
        ·
          refine ⟨116433756750824792919159799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155245009001099723892213065 116433756750824792919159799)
          ·
            refine ⟨174650635126237189378739699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116433756750824792919159799 174650635126237189378739699)
            ·
              refine ⟨261975952689355784068109549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174650635126237189378739699 261975952689355784068109549)
              ·
                refine ⟨98240982258508419025541081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261975952689355784068109549 98240982258508419025541081)
                ·
                  refine ⟨73680736693881314269155811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98240982258508419025541081 73680736693881314269155811)
                  ·
                    refine ⟨110521105040821971403733717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73680736693881314269155811 110521105040821971403733717)
                    ·
                      refine ⟨2590338399394264954775009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110521105040821971403733717 2590338399394264954775009)
                      ·
                        rfl

theorem cell23_5044666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_5044666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044666 prefixEnd_5044666 := by exact prefixLift 5044666
  have htrace : WordTrace (prefixWord ++ tailWord_5044666) baseStart_5044666 baseEnd_5044666 := by
    simpa [prefixWord, tailWord_5044666, baseEnd_5044666] using wordTrace_append hprefix tailTrace_5044666
  have hstable : (prefixWord ++ tailWord_5044666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044666).length < 2 ^ (prefixWord ++ tailWord_5044666).sum := by decide
  have hdescent : baseEnd_5044666 < baseStart_5044666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044680 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_5044680 : Nat := 118140960795 + 5044680 * 2 ^ 59
def prefixEnd_5044680 : Nat := 4983230072969 + 3 ^ 40 * 5044680 * 2
def baseEnd_5044680 : Nat := 2590345588123427899999945

theorem tailTrace_5044680 : CollatzResearch.WordTrace tailWord_5044680 prefixEnd_5044680 2590345588123427899999945 := by
  unfold tailWord_5044680
  simp only [CollatzResearch.WordTrace]
  refine ⟨91997297681996698798297747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122663063575995598397730329 91997297681996698798297747)
  ·
    refine ⟨137995946522995048197446621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91997297681996698798297747 137995946522995048197446621)
    ·
      refine ⟨51748479946123143074042483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137995946522995048197446621 51748479946123143074042483)
      ·
        refine ⟨77622719919184714611063725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51748479946123143074042483 77622719919184714611063725)
        ·
          refine ⟨29108519969694267979148897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77622719919184714611063725 29108519969694267979148897)
          ·
            refine ⟨21831389977270700984361673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29108519969694267979148897 21831389977270700984361673)
            ·
              refine ⟨16373542482953025738271255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21831389977270700984361673 16373542482953025738271255)
              ·
                refine ⟨24560313724429538607406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16373542482953025738271255 24560313724429538607406883)
                ·
                  refine ⟨36840470586644307911110325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24560313724429538607406883 36840470586644307911110325)
                  ·
                    refine ⟨3453794117497903866666593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36840470586644307911110325 3453794117497903866666593)
                    ·
                      refine ⟨2590345588123427899999945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453794117497903866666593 2590345588123427899999945)
                      ·
                        rfl

theorem cell23_5044680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_5044680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044680 prefixEnd_5044680 := by exact prefixLift 5044680
  have htrace : WordTrace (prefixWord ++ tailWord_5044680) baseStart_5044680 baseEnd_5044680 := by
    simpa [prefixWord, tailWord_5044680, baseEnd_5044680] using wordTrace_append hprefix tailTrace_5044680
  have hstable : (prefixWord ++ tailWord_5044680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044680).length < 2 ^ (prefixWord ++ tailWord_5044680).sum := by decide
  have hdescent : baseEnd_5044680 < baseStart_5044680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044704 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 1, 1, 3]
def baseStart_5044704 : Nat := 118140960795 + 5044704 * 2 ^ 59
def prefixEnd_5044704 : Nat := 4983230072969 + 3 ^ 40 * 5044704 * 2
def baseEnd_5044704 : Nat := 2590357911659135806099835

theorem tailTrace_5044704 : CollatzResearch.WordTrace tailWord_5044704 prefixEnd_5044704 2590357911659135806099835 := by
  unfold tailWord_5044704
  simp only [CollatzResearch.WordTrace]
  refine ⟨91997735357953224847734583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122663647143937633130312777 91997735357953224847734583)
  ·
    refine ⟨137996603036929837271601875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91997735357953224847734583 137996603036929837271601875)
    ·
      refine ⟨206994904555394755907402813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137996603036929837271601875 206994904555394755907402813)
      ·
        refine ⟨77623089208273033465276055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206994904555394755907402813 77623089208273033465276055)
        ·
          refine ⟨116434633812409550197914083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77623089208273033465276055 116434633812409550197914083)
          ·
            refine ⟨174651950718614325296871125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116434633812409550197914083 174651950718614325296871125)
            ·
              refine ⟨4093405094967523249145417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 174651950718614325296871125 4093405094967523249145417)
              ·
                refine ⟨3070053821225642436859063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4093405094967523249145417 3070053821225642436859063)
                ·
                  refine ⟨4605080731838463655288595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070053821225642436859063 4605080731838463655288595)
                  ·
                    refine ⟨6907621097757695482932893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4605080731838463655288595 6907621097757695482932893)
                    ·
                      refine ⟨2590357911659135806099835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907621097757695482932893 2590357911659135806099835)
                      ·
                        rfl

theorem cell23_5044704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_5044704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044704 prefixEnd_5044704 := by exact prefixLift 5044704
  have htrace : WordTrace (prefixWord ++ tailWord_5044704) baseStart_5044704 baseEnd_5044704 := by
    simpa [prefixWord, tailWord_5044704, baseEnd_5044704] using wordTrace_append hprefix tailTrace_5044704
  have hstable : (prefixWord ++ tailWord_5044704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044704).length < 2 ^ (prefixWord ++ tailWord_5044704).sum := by decide
  have hdescent : baseEnd_5044704 < baseStart_5044704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044720 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_5044720 : Nat := 118140960795 + 5044720 * 2 ^ 59
def prefixEnd_5044720 : Nat := 4983230072969 + 3 ^ 40 * 5044720 * 2
def baseEnd_5044720 : Nat := 863455375783202581166587

theorem tailTrace_5044720 : CollatzResearch.WordTrace tailWord_5044720 prefixEnd_5044720 863455375783202581166587 := by
  unfold tailWord_5044720
  simp only [CollatzResearch.WordTrace]
  refine ⟨91998027141924242214025807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122664036189232322952034409 91998027141924242214025807)
  ·
    refine ⟨137997040712886363321038711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91998027141924242214025807 137997040712886363321038711)
    ·
      refine ⟨206995561069329544981558067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137997040712886363321038711 206995561069329544981558067)
      ·
        refine ⟨310493341603994317472337101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206995561069329544981558067 310493341603994317472337101)
        ·
          refine ⟨116435003101497869052126413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310493341603994317472337101 116435003101497869052126413)
          ·
            refine ⟨43663126163061700894547405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116435003101497869052126413 43663126163061700894547405)
            ·
              refine ⟨16373672311148137835455277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43663126163061700894547405 16373672311148137835455277)
              ·
                refine ⟨6140127116680551688295729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16373672311148137835455277 6140127116680551688295729)
                ·
                  refine ⟨4605095337510413766221797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6140127116680551688295729 4605095337510413766221797)
                  ·
                    refine ⟨863455375783202581166587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4605095337510413766221797 863455375783202581166587)
                    ·
                      rfl

theorem cell23_5044720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_5044720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044720 prefixEnd_5044720 := by exact prefixLift 5044720
  have htrace : WordTrace (prefixWord ++ tailWord_5044720) baseStart_5044720 baseEnd_5044720 := by
    simpa [prefixWord, tailWord_5044720, baseEnd_5044720] using wordTrace_append hprefix tailTrace_5044720
  have hstable : (prefixWord ++ tailWord_5044720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044720).length < 2 ^ (prefixWord ++ tailWord_5044720).sum := by decide
  have hdescent : baseEnd_5044720 < baseStart_5044720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044723 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4]
def baseStart_5044723 : Nat := 118140960795 + 5044723 * 2 ^ 59
def prefixEnd_5044723 : Nat := 4983230072969 + 3 ^ 40 * 5044723 * 2
def baseEnd_5044723 : Nat := 2590367667791571231762247

theorem tailTrace_5044723 : CollatzResearch.WordTrace tailWord_5044723 prefixEnd_5044723 2590367667791571231762247 := by
  unfold tailWord_5044723
  simp only [CollatzResearch.WordTrace]
  refine ⟨183996163702837615940410823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122664109135225077293607215 183996163702837615940410823)
  ·
    refine ⟨275994245554256423910616235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183996163702837615940410823 275994245554256423910616235)
    ·
      refine ⟨413991368331384635865924353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275994245554256423910616235 413991368331384635865924353)
      ·
        refine ⟨310493526248538476899443265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413991368331384635865924353 310493526248538476899443265)
        ·
          refine ⟨232870144686403857674582449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310493526248538476899443265 232870144686403857674582449)
          ·
            refine ⟨174652608514802893255936837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232870144686403857674582449 174652608514802893255936837)
            ·
              refine ⟨32747364096525542485488157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174652608514802893255936837 32747364096525542485488157)
              ·
                refine ⟨12280261536197078432058059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32747364096525542485488157 12280261536197078432058059)
                ·
                  refine ⟨18420392304295617648087089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12280261536197078432058059 18420392304295617648087089)
                  ·
                    refine ⟨13815294228221713236065317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18420392304295617648087089 13815294228221713236065317)
                    ·
                      refine ⟨2590367667791571231762247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13815294228221713236065317 2590367667791571231762247)
                      ·
                        rfl

theorem cell23_5044723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_5044723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044723 prefixEnd_5044723 := by exact prefixLift 5044723
  have htrace : WordTrace (prefixWord ++ tailWord_5044723) baseStart_5044723 baseEnd_5044723 := by
    simpa [prefixWord, tailWord_5044723, baseEnd_5044723] using wordTrace_append hprefix tailTrace_5044723
  have hstable : (prefixWord ++ tailWord_5044723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044723).length < 2 ^ (prefixWord ++ tailWord_5044723).sum := by decide
  have hdescent : baseEnd_5044723 < baseStart_5044723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044730 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_5044730 : Nat := 118140960795 + 5044730 * 2 ^ 59
def prefixEnd_5044730 : Nat := 4983230072969 + 3 ^ 40 * 5044730 * 2
def baseEnd_5044730 : Nat := 2590371262156152704374715

theorem tailTrace_5044730 : CollatzResearch.WordTrace tailWord_5044730 prefixEnd_5044730 2590371262156152704374715 := by
  unfold tailWord_5044730
  simp only [CollatzResearch.WordTrace]
  refine ⟨45999104753453064033978911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122664279342541504090610429 45999104753453064033978911)
  ·
    refine ⟨68998657130179596050968367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45999104753453064033978911 68998657130179596050968367)
    ·
      refine ⟨103497985695269394076452551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68998657130179596050968367 103497985695269394076452551)
      ·
        refine ⟨155246978542904091114678827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103497985695269394076452551 155246978542904091114678827)
        ·
          refine ⟨232870467814356136672018241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155246978542904091114678827 232870467814356136672018241)
          ·
            refine ⟨174652850860767102504013681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232870467814356136672018241 174652850860767102504013681)
            ·
              refine ⟨130989638145575326878010261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174652850860767102504013681 130989638145575326878010261)
              ·
                refine ⟨6140139288073843447406731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130989638145575326878010261 6140139288073843447406731)
                ·
                  refine ⟨9210208932110765171110097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140139288073843447406731 9210208932110765171110097)
                  ·
                    refine ⟨6907656699083073878332573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9210208932110765171110097 6907656699083073878332573)
                    ·
                      refine ⟨2590371262156152704374715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907656699083073878332573 2590371262156152704374715)
                      ·
                        rfl

theorem cell23_5044730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_5044730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044730 prefixEnd_5044730 := by exact prefixLift 5044730
  have htrace : WordTrace (prefixWord ++ tailWord_5044730) baseStart_5044730 baseEnd_5044730 := by
    simpa [prefixWord, tailWord_5044730, baseEnd_5044730] using wordTrace_append hprefix tailTrace_5044730
  have hstable : (prefixWord ++ tailWord_5044730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044730).length < 2 ^ (prefixWord ++ tailWord_5044730).sum := by decide
  have hdescent : baseEnd_5044730 < baseStart_5044730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044740 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5044740 : Nat := 118140960795 + 5044740 * 2 ^ 59
def prefixEnd_5044740 : Nat := 4983230072969 + 3 ^ 40 * 5044740 * 2
def baseEnd_5044740 : Nat := 2590376396962697665249669

theorem tailTrace_5044740 : CollatzResearch.WordTrace tailWord_5044740 prefixEnd_5044740 2590376396962697665249669 := by
  unfold tailWord_5044740
  simp only [CollatzResearch.WordTrace]
  refine ⟨91998391871888013921889837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122664522495850685229186449 91998391871888013921889837)
  ·
    refine ⟨34499396951958005220708689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91998391871888013921889837 34499396951958005220708689)
    ·
      refine ⟨25874547713968503915531517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34499396951958005220708689 25874547713968503915531517)
      ·
        refine ⟨9702955392738188968324319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25874547713968503915531517 9702955392738188968324319)
        ·
          refine ⟨14554433089107283452486479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9702955392738188968324319 14554433089107283452486479)
          ·
            refine ⟨21831649633660925178729719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14554433089107283452486479 21831649633660925178729719)
            ·
              refine ⟨32747474450491387768094579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21831649633660925178729719 32747474450491387768094579)
              ·
                refine ⟨49121211675737081652141869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32747474450491387768094579 49121211675737081652141869)
                ·
                  refine ⟨18420454378401405619553201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49121211675737081652141869 18420454378401405619553201)
                  ·
                    refine ⟨13815340783801054214664901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18420454378401405619553201 13815340783801054214664901)
                    ·
                      refine ⟨2590376396962697665249669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13815340783801054214664901 2590376396962697665249669)
                      ·
                        rfl

theorem cell23_5044740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5044740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044740 prefixEnd_5044740 := by exact prefixLift 5044740
  have htrace : WordTrace (prefixWord ++ tailWord_5044740) baseStart_5044740 baseEnd_5044740 := by
    simpa [prefixWord, tailWord_5044740, baseEnd_5044740] using wordTrace_append hprefix tailTrace_5044740
  have hstable : (prefixWord ++ tailWord_5044740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044740).length < 2 ^ (prefixWord ++ tailWord_5044740).sum := by decide
  have hdescent : baseEnd_5044740 < baseStart_5044740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044744 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_5044744 : Nat := 118140960795 + 5044744 * 2 ^ 59
def prefixEnd_5044744 : Nat := 4983230072969 + 3 ^ 40 * 5044744 * 2
def baseEnd_5044744 : Nat := 2590378450885315649599651

theorem tailTrace_5044744 : CollatzResearch.WordTrace tailWord_5044744 prefixEnd_5044744 2590378450885315649599651 := by
  unfold tailWord_5044744
  simp only [CollatzResearch.WordTrace]
  refine ⟨91998464817880768263462643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122664619757174357684616857 91998464817880768263462643)
  ·
    refine ⟨137997697226821152395193965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91998464817880768263462643 137997697226821152395193965)
    ·
      refine ⟨51749136460057932148197737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137997697226821152395193965 51749136460057932148197737)
      ·
        refine ⟨38811852345043449111148303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51749136460057932148197737 38811852345043449111148303)
        ·
          refine ⟨58217778517565173666722455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38811852345043449111148303 58217778517565173666722455)
          ·
            refine ⟨87326667776347760500083683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58217778517565173666722455 87326667776347760500083683)
            ·
              refine ⟨130990001664521640750125525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87326667776347760500083683 130990001664521640750125525)
              ·
                refine ⟨3070078164012225955081067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130990001664521640750125525 3070078164012225955081067)
                ·
                  refine ⟨4605117246018338932621601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070078164012225955081067 4605117246018338932621601)
                  ·
                    refine ⟨3453837934513754199466201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4605117246018338932621601 3453837934513754199466201)
                    ·
                      refine ⟨2590378450885315649599651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453837934513754199466201 2590378450885315649599651)
                      ·
                        rfl

theorem cell23_5044744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_5044744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044744 prefixEnd_5044744 := by exact prefixLift 5044744
  have htrace : WordTrace (prefixWord ++ tailWord_5044744) baseStart_5044744 baseEnd_5044744 := by
    simpa [prefixWord, tailWord_5044744, baseEnd_5044744] using wordTrace_append hprefix tailTrace_5044744
  have hstable : (prefixWord ++ tailWord_5044744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044744).length < 2 ^ (prefixWord ++ tailWord_5044744).sum := by decide
  have hdescent : baseEnd_5044744 < baseStart_5044744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044787 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 1, 3, 2]
def baseStart_5044787 : Nat := 118140960795 + 5044787 * 2 ^ 59
def prefixEnd_5044787 : Nat := 4983230072969 + 3 ^ 40 * 5044787 * 2
def baseEnd_5044787 : Nat := 2590400530553458981361953

theorem tailTrace_5044787 : CollatzResearch.WordTrace tailWord_5044787 prefixEnd_5044787 2590400530553458981361953 := by
  unfold tailWord_5044787
  simp only [CollatzResearch.WordTrace]
  refine ⟨183998497974605754870740615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122665665316403836580493743 183998497974605754870740615)
  ·
    refine ⟨275997746961908632306110923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183998497974605754870740615 275997746961908632306110923)
    ·
      refine ⟨413996620442862948459166385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275997746961908632306110923 413996620442862948459166385)
      ·
        refine ⟨310497465332147211344374789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413996620442862948459166385 310497465332147211344374789)
        ·
          refine ⟨58218274749777602127070273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310497465332147211344374789 58218274749777602127070273)
          ·
            refine ⟨43663706062333201595302705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58218274749777602127070273 43663706062333201595302705)
            ·
              refine ⟨32747779546749901196477029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43663706062333201595302705 32747779546749901196477029)
              ·
                refine ⟨6140208665015606474339443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32747779546749901196477029 6140208665015606474339443)
                ·
                  refine ⟨9210312997523409711509165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140208665015606474339443 9210312997523409711509165)
                  ·
                    refine ⟨3453867374071278641815937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9210312997523409711509165 3453867374071278641815937)
                    ·
                      refine ⟨2590400530553458981361953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3453867374071278641815937 2590400530553458981361953)
                      ·
                        rfl

theorem cell23_5044787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3, 2].length) (baseStart_5044787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044787 prefixEnd_5044787 := by exact prefixLift 5044787
  have htrace : WordTrace (prefixWord ++ tailWord_5044787) baseStart_5044787 baseEnd_5044787 := by
    simpa [prefixWord, tailWord_5044787, baseEnd_5044787] using wordTrace_append hprefix tailTrace_5044787
  have hstable : (prefixWord ++ tailWord_5044787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044787).length < 2 ^ (prefixWord ++ tailWord_5044787).sum := by decide
  have hdescent : baseEnd_5044787 < baseStart_5044787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044793 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_5044793 : Nat := 118140960795 + 5044793 * 2 ^ 59
def prefixEnd_5044793 : Nat := 4983230072969 + 3 ^ 40 * 5044793 * 2
def baseEnd_5044793 : Nat := 863467870479128652628975

theorem tailTrace_5044793 : CollatzResearch.WordTrace tailWord_5044793 prefixEnd_5044793 863467870479128652628975 := by
  unfold tailWord_5044793
  simp only [CollatzResearch.WordTrace]
  refine ⟨183998716812584017895459033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122665811208389345263639355 183998716812584017895459033)
  ·
    refine ⟨137999037609438013421594275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183998716812584017895459033 137999037609438013421594275)
    ·
      refine ⟨206998556414157020132391413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137999037609438013421594275 206998556414157020132391413)
      ·
        refine ⟨19406114663827220637411695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206998556414157020132391413 19406114663827220637411695)
        ·
          refine ⟨29109171995740830956117543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19406114663827220637411695 29109171995740830956117543)
          ·
            refine ⟨43663757993611246434176315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29109171995740830956117543 43663757993611246434176315)
            ·
              refine ⟨65495636990416869651264473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43663757993611246434176315 65495636990416869651264473)
              ·
                refine ⟨49121727742812652238448355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65495636990416869651264473 49121727742812652238448355)
                ·
                  refine ⟨73682591614218978357672533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49121727742812652238448355 73682591614218978357672533)
                  ·
                    refine ⟨863467870479128652628975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73682591614218978357672533 863467870479128652628975)
                    ·
                      rfl

theorem cell23_5044793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_5044793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044793 prefixEnd_5044793 := by exact prefixLift 5044793
  have htrace : WordTrace (prefixWord ++ tailWord_5044793) baseStart_5044793 baseEnd_5044793 := by
    simpa [prefixWord, tailWord_5044793, baseEnd_5044793] using wordTrace_append hprefix tailTrace_5044793
  have hstable : (prefixWord ++ tailWord_5044793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044793).length < 2 ^ (prefixWord ++ tailWord_5044793).sum := by decide
  have hdescent : baseEnd_5044793 < baseStart_5044793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044798 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5044798 : Nat := 118140960795 + 5044798 * 2 ^ 59
def prefixEnd_5044798 : Nat := 4983230072969 + 3 ^ 40 * 5044798 * 2
def baseEnd_5044798 : Nat := 2590406178840658438324403

theorem tailTrace_5044798 : CollatzResearch.WordTrace tailWord_5044798 prefixEnd_5044798 2590406178840658438324403 := by
  unfold tailWord_5044798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22999862397195737968673881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122665932785043935832927365 22999862397195737968673881)
  ·
    refine ⟨17249896797896803476505411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22999862397195737968673881 17249896797896803476505411)
    ·
      refine ⟨25874845196845205214758117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17249896797896803476505411 25874845196845205214758117)
      ·
        refine ⟨4851533474408475977767147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25874845196845205214758117 4851533474408475977767147)
        ·
          refine ⟨7277300211612713966650721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851533474408475977767147 7277300211612713966650721)
          ·
            refine ⟨5457975158709535474988041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7277300211612713966650721 5457975158709535474988041)
            ·
              refine ⟨4093481369032151606241031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5457975158709535474988041 4093481369032151606241031)
              ·
                refine ⟨6140222053548227409361547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093481369032151606241031 6140222053548227409361547)
                ·
                  refine ⟨9210333080322341114042321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140222053548227409361547 9210333080322341114042321)
                  ·
                    refine ⟨6907749810241755835531741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9210333080322341114042321 6907749810241755835531741)
                    ·
                      refine ⟨2590406178840658438324403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907749810241755835531741 2590406178840658438324403)
                      ·
                        rfl

theorem cell23_5044798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5044798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044798 prefixEnd_5044798 := by exact prefixLift 5044798
  have htrace : WordTrace (prefixWord ++ tailWord_5044798) baseStart_5044798 baseEnd_5044798 := by
    simpa [prefixWord, tailWord_5044798, baseEnd_5044798] using wordTrace_append hprefix tailTrace_5044798
  have hstable : (prefixWord ++ tailWord_5044798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044798).length < 2 ^ (prefixWord ++ tailWord_5044798).sum := by decide
  have hdescent : baseEnd_5044798 < baseStart_5044798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044803 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_5044803 : Nat := 118140960795 + 5044803 * 2 ^ 59
def prefixEnd_5044803 : Nat := 4983230072969 + 3 ^ 40 * 5044803 * 2
def baseEnd_5044803 : Nat := 2590408746243930918761879

theorem tailTrace_5044803 : CollatzResearch.WordTrace tailWord_5044803 prefixEnd_5044803 2590408746243930918761879 := by
  unfold tailWord_5044803
  simp only [CollatzResearch.WordTrace]
  refine ⟨183999081542547789603323063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122666054361698526402215375 183999081542547789603323063)
  ·
    refine ⟨275998622313821684404984595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183999081542547789603323063 275998622313821684404984595)
    ·
      refine ⟨413997933470732526607476893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275998622313821684404984595 413997933470732526607476893)
      ·
        refine ⟨155249225051524697477803835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413997933470732526607476893 155249225051524697477803835)
        ·
          refine ⟨232873837577287046216705753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155249225051524697477803835 232873837577287046216705753)
          ·
            refine ⟨174655378182965284662529315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232873837577287046216705753 174655378182965284662529315)
            ·
              refine ⟨261983067274447926993793973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174655378182965284662529315 261983067274447926993793973)
              ·
                refine ⟨24560912556979493155668185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261983067274447926993793973 24560912556979493155668185)
                ·
                  refine ⟨18420684417734619866751139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24560912556979493155668185 18420684417734619866751139)
                  ·
                    refine ⟨27631026626601929800126709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18420684417734619866751139 27631026626601929800126709)
                    ·
                      refine ⟨2590408746243930918761879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27631026626601929800126709 2590408746243930918761879)
                      ·
                        rfl

theorem cell23_5044803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_5044803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044803 prefixEnd_5044803 := by exact prefixLift 5044803
  have htrace : WordTrace (prefixWord ++ tailWord_5044803) baseStart_5044803 baseEnd_5044803 := by
    simpa [prefixWord, tailWord_5044803, baseEnd_5044803] using wordTrace_append hprefix tailTrace_5044803
  have hstable : (prefixWord ++ tailWord_5044803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044803).length < 2 ^ (prefixWord ++ tailWord_5044803).sum := by decide
  have hdescent : baseEnd_5044803 < baseStart_5044803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044857 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 5]
def baseStart_5044857 : Nat := 118140960795 + 5044857 * 2 ^ 59
def prefixEnd_5044857 : Nat := 4983230072969 + 3 ^ 40 * 5044857 * 2
def baseEnd_5044857 : Nat := 287826274911030411942959

theorem tailTrace_5044857 : CollatzResearch.WordTrace tailWord_5044857 prefixEnd_5044857 287826274911030411942959 := by
  unfold tailWord_5044857
  simp only [CollatzResearch.WordTrace]
  refine ⟨184001051084352156825788825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122667367389568104550525883 184001051084352156825788825)
  ·
    refine ⟨138000788313264117619341619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184001051084352156825788825 138000788313264117619341619)
    ·
      refine ⟨207001182469896176429012429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138000788313264117619341619 207001182469896176429012429)
      ·
        refine ⟨77625443426211066160879661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207001182469896176429012429 77625443426211066160879661)
        ·
          refine ⟨29109541284829149810329873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77625443426211066160879661 29109541284829149810329873)
          ·
            refine ⟨21832155963621862357747405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29109541284829149810329873 21832155963621862357747405)
            ·
              refine ⟨8187058486358198384155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21832155963621862357747405 8187058486358198384155277)
              ·
                refine ⟨3070146932384324394058229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8187058486358198384155277 3070146932384324394058229)
                ·
                  refine ⟨287826274911030411942959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070146932384324394058229 287826274911030411942959)
                  ·
                    rfl

theorem cell23_5044857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 5].length) (baseStart_5044857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044857 prefixEnd_5044857 := by exact prefixLift 5044857
  have htrace : WordTrace (prefixWord ++ tailWord_5044857) baseStart_5044857 baseEnd_5044857 := by
    simpa [prefixWord, tailWord_5044857, baseEnd_5044857] using wordTrace_append hprefix tailTrace_5044857
  have hstable : (prefixWord ++ tailWord_5044857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044857).length < 2 ^ (prefixWord ++ tailWord_5044857).sum := by decide
  have hdescent : baseEnd_5044857 < baseStart_5044857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044874 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_5044874 : Nat := 118140960795 + 5044874 * 2 ^ 59
def prefixEnd_5044874 : Nat := 4983230072969 + 3 ^ 40 * 5044874 * 2
def baseEnd_5044874 : Nat := 287827244818933348997117

theorem tailTrace_5044874 : CollatzResearch.WordTrace tailWord_5044874 prefixEnd_5044874 287827244818933348997117 := by
  unfold tailWord_5044874
  simp only [CollatzResearch.WordTrace]
  refine ⟨46000417781322642182289419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122667780750193712486105117 46000417781322642182289419)
  ·
    refine ⟨69000626671983963273434129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46000417781322642182289419 69000626671983963273434129)
    ·
      refine ⟨51750470003987972455075597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69000626671983963273434129 51750470003987972455075597)
      ·
        refine ⟨19406426251495489670653349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51750470003987972455075597 19406426251495489670653349)
        ·
          refine ⟨3638704922155404313247503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19406426251495489670653349 3638704922155404313247503)
          ·
            refine ⟨5458057383233106469871255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3638704922155404313247503 5458057383233106469871255)
            ·
              refine ⟨8187086074849659704806883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458057383233106469871255 8187086074849659704806883)
              ·
                refine ⟨12280629112274489557210325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8187086074849659704806883 12280629112274489557210325)
                ·
                  refine ⟨287827244818933348997117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12280629112274489557210325 287827244818933348997117)
                  ·
                    rfl

theorem cell23_5044874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_5044874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044874 prefixEnd_5044874 := by exact prefixLift 5044874
  have htrace : WordTrace (prefixWord ++ tailWord_5044874) baseStart_5044874 baseEnd_5044874 := by
    simpa [prefixWord, tailWord_5044874, baseEnd_5044874] using wordTrace_append hprefix tailTrace_5044874
  have hstable : (prefixWord ++ tailWord_5044874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044874).length < 2 ^ (prefixWord ++ tailWord_5044874).sum := by decide
  have hdescent : baseEnd_5044874 < baseStart_5044874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044927 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_5044927 : Nat := 118140960795 + 5044927 * 2 ^ 59
def prefixEnd_5044927 : Nat := 4983230072969 + 3 ^ 40 * 5044927 * 2
def baseEnd_5044927 : Nat := 2590472417845088433611309

theorem tailTrace_5044927 : CollatzResearch.WordTrace tailWord_5044927 prefixEnd_5044927 2590472417845088433611309 := by
  unfold tailWord_5044927
  simp only [CollatzResearch.WordTrace]
  refine ⟨184003604194098558780837035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122669069462732372520558023 184003604194098558780837035)
  ·
    refine ⟨276005406291147838171255553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184003604194098558780837035 276005406291147838171255553)
    ·
      refine ⟨207004054718360878628441665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276005406291147838171255553 207004054718360878628441665)
      ·
        refine ⟨155253041038770658971331249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207004054718360878628441665 155253041038770658971331249)
        ·
          refine ⟨116439780779077994228498437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155253041038770658971331249 116439780779077994228498437)
          ·
            refine ⟨21832458896077123917843457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116439780779077994228498437 21832458896077123917843457)
            ·
              refine ⟨16374344172057842938382593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21832458896077123917843457 16374344172057842938382593)
              ·
                refine ⟨12280758129043382203786945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16374344172057842938382593 12280758129043382203786945)
                ·
                  refine ⟨9210568596782536652840209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12280758129043382203786945 9210568596782536652840209)
                  ·
                    refine ⟨6907926447586902489630157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9210568596782536652840209 6907926447586902489630157)
                    ·
                      refine ⟨2590472417845088433611309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6907926447586902489630157 2590472417845088433611309)
                      ·
                        rfl

theorem cell23_5044927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_5044927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044927 prefixEnd_5044927 := by exact prefixLift 5044927
  have htrace : WordTrace (prefixWord ++ tailWord_5044927) baseStart_5044927 baseEnd_5044927 := by
    simpa [prefixWord, tailWord_5044927, baseEnd_5044927] using wordTrace_append hprefix tailTrace_5044927
  have hstable : (prefixWord ++ tailWord_5044927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044927).length < 2 ^ (prefixWord ++ tailWord_5044927).sum := by decide
  have hdescent : baseEnd_5044927 < baseStart_5044927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044970 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5044970 : Nat := 118140960795 + 5044970 * 2 ^ 59
def prefixEnd_5044970 : Nat := 4983230072969 + 3 ^ 40 * 5044970 * 2
def baseEnd_5044970 : Nat := 2590494497513231765373611

theorem tailTrace_5044970 : CollatzResearch.WordTrace tailWord_5044970 prefixEnd_5044970 2590494497513231765373611 := by
  unfold tailWord_5044970
  simp only [CollatzResearch.WordTrace]
  refine ⟨46001293133235694281163091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122670115021961851416434909 46001293133235694281163091)
  ·
    refine ⟨69001939699853541421744637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46001293133235694281163091 69001939699853541421744637)
    ·
      refine ⟨25875727387445078033154239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69001939699853541421744637 25875727387445078033154239)
      ·
        refine ⟨38813591081167617049731359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25875727387445078033154239 38813591081167617049731359)
        ·
          refine ⟨58220386621751425574597039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38813591081167617049731359 58220386621751425574597039)
          ·
            refine ⟨87330579932627138361895559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58220386621751425574597039 87330579932627138361895559)
            ·
              refine ⟨130995869898940707542843339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87330579932627138361895559 130995869898940707542843339)
              ·
                refine ⟨196493804848411061314265009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130995869898940707542843339 196493804848411061314265009)
                ·
                  refine ⟨147370353636308295985698757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196493804848411061314265009 147370353636308295985698757)
                  ·
                    refine ⟨27631941306807805497318517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147370353636308295985698757 27631941306807805497318517)
                    ·
                      refine ⟨2590494497513231765373611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27631941306807805497318517 2590494497513231765373611)
                      ·
                        rfl

theorem cell23_5044970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5044970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044970 prefixEnd_5044970 := by exact prefixLift 5044970
  have htrace : WordTrace (prefixWord ++ tailWord_5044970) baseStart_5044970 baseEnd_5044970 := by
    simpa [prefixWord, tailWord_5044970, baseEnd_5044970] using wordTrace_append hprefix tailTrace_5044970
  have hstable : (prefixWord ++ tailWord_5044970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044970).length < 2 ^ (prefixWord ++ tailWord_5044970).sum := by decide
  have hdescent : baseEnd_5044970 < baseStart_5044970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044977 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_5044977 : Nat := 118140960795 + 5044977 * 2 ^ 59
def prefixEnd_5044977 : Nat := 4983230072969 + 3 ^ 40 * 5044977 * 2
def baseEnd_5044977 : Nat := 863499363959271079328693

theorem tailTrace_5044977 : CollatzResearch.WordTrace tailWord_5044977 prefixEnd_5044977 863499363959271079328693 := by
  unfold tailWord_5044977
  simp only [CollatzResearch.WordTrace]
  refine ⟨184005427843917417320157185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122670285229278278213438123 184005427843917417320157185)
  ·
    refine ⟨138004070882938062990117889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184005427843917417320157185 138004070882938062990117889)
    ·
      refine ⟨103503053162203547242588417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138004070882938062990117889 103503053162203547242588417)
      ·
        refine ⟨77627289871652660431941313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103503053162203547242588417 77627289871652660431941313)
        ·
          refine ⟨58220467403739495323955985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77627289871652660431941313 58220467403739495323955985)
          ·
            refine ⟨43665350552804621492966989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58220467403739495323955985 43665350552804621492966989)
            ·
              refine ⟨16374506457301733059862621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43665350552804621492966989 16374506457301733059862621)
              ·
                refine ⟨6140439921488149897448483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16374506457301733059862621 6140439921488149897448483)
                ·
                  refine ⟨9210659882232224846172725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140439921488149897448483 9210659882232224846172725)
                  ·
                    refine ⟨863499363959271079328693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9210659882232224846172725 863499363959271079328693)
                    ·
                      rfl

theorem cell23_5044977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_5044977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044977 prefixEnd_5044977 := by exact prefixLift 5044977
  have htrace : WordTrace (prefixWord ++ tailWord_5044977) baseStart_5044977 baseEnd_5044977 := by
    simpa [prefixWord, tailWord_5044977, baseEnd_5044977] using wordTrace_append hprefix tailTrace_5044977
  have hstable : (prefixWord ++ tailWord_5044977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044977).length < 2 ^ (prefixWord ++ tailWord_5044977).sum := by decide
  have hdescent : baseEnd_5044977 < baseStart_5044977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5044981 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 8]
def baseStart_5044981 : Nat := 118140960795 + 5044981 * 2 ^ 59
def prefixEnd_5044981 : Nat := 4983230072969 + 3 ^ 40 * 5044981 * 2
def baseEnd_5044981 : Nat := 287833349533381246926229

theorem tailTrace_5044981 : CollatzResearch.WordTrace tailWord_5044981 prefixEnd_5044981 287833349533381246926229 := by
  unfold tailWord_5044981
  simp only [CollatzResearch.WordTrace]
  refine ⟨184005573735902926003302797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122670382490601950668868531 184005573735902926003302797)
  ·
    refine ⟨69002090150963597251238549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184005573735902926003302797 69002090150963597251238549)
    ·
      refine ⟨3234472975826418621151807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69002090150963597251238549 3234472975826418621151807)
      ·
        refine ⟨4851709463739627931727711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234472975826418621151807 4851709463739627931727711)
        ·
          refine ⟨7277564195609441897591567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851709463739627931727711 7277564195609441897591567)
          ·
            refine ⟨10916346293414162846387351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277564195609441897591567 10916346293414162846387351)
            ·
              refine ⟨16374519440121244269581027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10916346293414162846387351 16374519440121244269581027)
              ·
                refine ⟨24561779160181866404371541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16374519440121244269581027 24561779160181866404371541)
                ·
                  refine ⟨287833349533381246926229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24561779160181866404371541 287833349533381246926229)
                  ·
                    rfl

theorem cell23_5044981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_5044981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5044981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5044981 prefixEnd_5044981 := by exact prefixLift 5044981
  have htrace : WordTrace (prefixWord ++ tailWord_5044981) baseStart_5044981 baseEnd_5044981 := by
    simpa [prefixWord, tailWord_5044981, baseEnd_5044981] using wordTrace_append hprefix tailTrace_5044981
  have hstable : (prefixWord ++ tailWord_5044981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5044981).length < 2 ^ (prefixWord ++ tailWord_5044981).sum := by decide
  have hdescent : baseEnd_5044981 < baseStart_5044981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5044981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045054 : List Nat := [4, 2, 1, 2, 3, 1, 2, 8]
def baseStart_5045054 : Nat := 118140960795 + 5045054 * 2 ^ 59
def prefixEnd_5045054 : Nat := 4983230072969 + 3 ^ 40 * 5045054 * 2
def baseEnd_5045054 : Nat := 95945838144007756915675

theorem tailTrace_5045054 : CollatzResearch.WordTrace tailWord_5045054 prefixEnd_5045054 95945838144007756915675 := by
  unfold tailWord_5045054
  simp only [CollatzResearch.WordTrace]
  refine ⟨23001029533079807433838777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122672157509758972980473477 23001029533079807433838777)
  ·
    refine ⟨17250772149809855575379083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23001029533079807433838777 17250772149809855575379083)
    ·
      refine ⟨25876158224714783363068625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17250772149809855575379083 25876158224714783363068625)
      ·
        refine ⟨19407118668536087522301469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25876158224714783363068625 19407118668536087522301469)
        ·
          refine ⟨7277669500701032820863051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19407118668536087522301469 7277669500701032820863051)
          ·
            refine ⟨10916504251051549231294577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7277669500701032820863051 10916504251051549231294577)
            ·
              refine ⟨8187378188288661923470933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10916504251051549231294577 8187378188288661923470933)
              ·
                refine ⟨95945838144007756915675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8187378188288661923470933 95945838144007756915675)
                ·
                  rfl

theorem cell23_5045054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_5045054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045054 prefixEnd_5045054 := by exact prefixLift 5045054
  have htrace : WordTrace (prefixWord ++ tailWord_5045054) baseStart_5045054 baseEnd_5045054 := by
    simpa [prefixWord, tailWord_5045054, baseEnd_5045054] using wordTrace_append hprefix tailTrace_5045054
  have hstable : (prefixWord ++ tailWord_5045054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045054).length < 2 ^ (prefixWord ++ tailWord_5045054).sum := by decide
  have hdescent : baseEnd_5045054 < baseStart_5045054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045107 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3]
def baseStart_5045107 : Nat := 118140960795 + 5045107 * 2 ^ 59
def prefixEnd_5045107 : Nat := 4983230072969 + 3 ^ 40 * 5045107 * 2
def baseEnd_5045107 : Nat := 2590564844362897729360481

theorem tailTrace_5045107 : CollatzResearch.WordTrace tailWord_5045107 prefixEnd_5045107 2590564844362897729360481 := by
  unfold tailWord_5045107
  simp only [CollatzResearch.WordTrace]
  refine ⟨184010169333446449522389575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122673446222297633014926383 184010169333446449522389575)
  ·
    refine ⟨276015254000169674283584363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184010169333446449522389575 276015254000169674283584363)
    ·
      refine ⟨414022881000254511425376545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276015254000169674283584363 414022881000254511425376545)
      ·
        refine ⟨310517160750190883569032409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414022881000254511425376545 310517160750190883569032409)
        ·
          refine ⟨232887870562643162676774307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310517160750190883569032409 232887870562643162676774307)
          ·
            refine ⟨349331805843964744015161461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232887870562643162676774307 349331805843964744015161461)
            ·
              refine ⟨32749856797871694751421387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 349331805843964744015161461 32749856797871694751421387)
              ·
                refine ⟨49124785196807542127132081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32749856797871694751421387 49124785196807542127132081)
                ·
                  refine ⟨36843588897605656595349061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49124785196807542127132081 36843588897605656595349061)
                  ·
                    refine ⟨6908172918301060611627949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36843588897605656595349061 6908172918301060611627949)
                    ·
                      refine ⟨2590564844362897729360481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908172918301060611627949 2590564844362897729360481)
                      ·
                        rfl

theorem cell23_5045107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_5045107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045107 prefixEnd_5045107 := by exact prefixLift 5045107
  have htrace : WordTrace (prefixWord ++ tailWord_5045107) baseStart_5045107 baseEnd_5045107 := by
    simpa [prefixWord, tailWord_5045107, baseEnd_5045107] using wordTrace_append hprefix tailTrace_5045107
  have hstable : (prefixWord ++ tailWord_5045107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045107).length < 2 ^ (prefixWord ++ tailWord_5045107).sum := by decide
  have hdescent : baseEnd_5045107 < baseStart_5045107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045117 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5045117 : Nat := 118140960795 + 5045117 * 2 ^ 59
def prefixEnd_5045117 : Nat := 4983230072969 + 3 ^ 40 * 5045117 * 2
def baseEnd_5045117 : Nat := 2590569979169442690235435

theorem tailTrace_5045117 : CollatzResearch.WordTrace tailWord_5045117 prefixEnd_5045117 2590569979169442690235435 := by
  unfold tailWord_5045117
  simp only [CollatzResearch.WordTrace]
  refine ⟨184010534063410221230253605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122673689375606814153502403 184010534063410221230253605)
  ·
    refine ⟨34501975136889416480672551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184010534063410221230253605 34501975136889416480672551)
    ·
      refine ⟨51752962705334124721008827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34501975136889416480672551 51752962705334124721008827)
      ·
        refine ⟨77629444058001187081513241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51752962705334124721008827 77629444058001187081513241)
        ·
          refine ⟨58222083043500890311134931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77629444058001187081513241 58222083043500890311134931)
          ·
            refine ⟨87333124565251335466702397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58222083043500890311134931 87333124565251335466702397)
            ·
              refine ⟨32749921711969250800013399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87333124565251335466702397 32749921711969250800013399)
              ·
                refine ⟨49124882567953876200020099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32749921711969250800013399 49124882567953876200020099)
                ·
                  refine ⟨73687323851930814300030149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49124882567953876200020099 73687323851930814300030149)
                  ·
                    refine ⟨13816373222237027681255653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73687323851930814300030149 13816373222237027681255653)
                    ·
                      refine ⟨2590569979169442690235435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13816373222237027681255653 2590569979169442690235435)
                      ·
                        rfl

theorem cell23_5045117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5045117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045117 prefixEnd_5045117 := by exact prefixLift 5045117
  have htrace : WordTrace (prefixWord ++ tailWord_5045117) baseStart_5045117 baseEnd_5045117 := by
    simpa [prefixWord, tailWord_5045117, baseEnd_5045117] using wordTrace_append hprefix tailTrace_5045117
  have hstable : (prefixWord ++ tailWord_5045117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045117).length < 2 ^ (prefixWord ++ tailWord_5045117).sum := by decide
  have hdescent : baseEnd_5045117 < baseStart_5045117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045127 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 9]
def baseStart_5045127 : Nat := 118140960795 + 5045127 * 2 ^ 59
def prefixEnd_5045127 : Nat := 4983230072969 + 3 ^ 40 * 5045127 * 2
def baseEnd_5045127 : Nat := 287841679330665294567821

theorem tailTrace_5045127 : CollatzResearch.WordTrace tailWord_5045127 prefixEnd_5045127 287841679330665294567821 := by
  unfold tailWord_5045127
  simp only [CollatzResearch.WordTrace]
  refine ⟨184010898793373992938117635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122673932528915995292078423 184010898793373992938117635)
  ·
    refine ⟨276016348190060989407176453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184010898793373992938117635 276016348190060989407176453)
    ·
      refine ⟨51753065285636435513845585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276016348190060989407176453 51753065285636435513845585)
      ·
        refine ⟨38814798964227326635384189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51753065285636435513845585 38814798964227326635384189)
        ·
          refine ⟨14555549611585247488269071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38814798964227326635384189 14555549611585247488269071)
          ·
            refine ⟨21833324417377871232403607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14555549611585247488269071 21833324417377871232403607)
            ·
              refine ⟨32749986626066806848605411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21833324417377871232403607 32749986626066806848605411)
              ·
                refine ⟨49124979939100210272908117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32749986626066806848605411 49124979939100210272908117)
                ·
                  refine ⟨287841679330665294567821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49124979939100210272908117 287841679330665294567821)
                  ·
                    rfl

theorem cell23_5045127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 9].length) (baseStart_5045127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045127 prefixEnd_5045127 := by exact prefixLift 5045127
  have htrace : WordTrace (prefixWord ++ tailWord_5045127) baseStart_5045127 baseEnd_5045127 := by
    simpa [prefixWord, tailWord_5045127, baseEnd_5045127] using wordTrace_append hprefix tailTrace_5045127
  have hstable : (prefixWord ++ tailWord_5045127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045127).length < 2 ^ (prefixWord ++ tailWord_5045127).sum := by decide
  have hdescent : baseEnd_5045127 < baseStart_5045127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045137 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_5045137 : Nat := 118140960795 + 5045137 * 2 ^ 59
def prefixEnd_5045137 : Nat := 4983230072969 + 3 ^ 40 * 5045137 * 2
def baseEnd_5045137 : Nat := 2590580248782532611985343

theorem tailTrace_5045137 : CollatzResearch.WordTrace tailWord_5045137 prefixEnd_5045137 2590580248782532611985343 := by
  unfold tailWord_5045137
  simp only [CollatzResearch.WordTrace]
  refine ⟨184011263523337764645981665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122674175682225176430654443 184011263523337764645981665)
  ·
    refine ⟨138008447642503323484486249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184011263523337764645981665 138008447642503323484486249)
    ·
      refine ⟨103506335731877492613364687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138008447642503323484486249 103506335731877492613364687)
      ·
        refine ⟨155259503597816238920047031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103506335731877492613364687 155259503597816238920047031)
        ·
          refine ⟨232889255396724358380070547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155259503597816238920047031 232889255396724358380070547)
          ·
            refine ⟨349333883095086537570105821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232889255396724358380070547 349333883095086537570105821)
            ·
              refine ⟨131000206160657451588789683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349333883095086537570105821 131000206160657451588789683)
              ·
                refine ⟨196500309240986177383184525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131000206160657451588789683 196500309240986177383184525)
                ·
                  refine ⟨73687615965369816518694197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196500309240986177383184525 73687615965369816518694197)
                  ·
                    refine ⟨6908213996753420298627581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73687615965369816518694197 6908213996753420298627581)
                    ·
                      refine ⟨2590580248782532611985343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908213996753420298627581 2590580248782532611985343)
                      ·
                        rfl

theorem cell23_5045137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_5045137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045137 prefixEnd_5045137 := by exact prefixLift 5045137
  have htrace : WordTrace (prefixWord ++ tailWord_5045137) baseStart_5045137 baseEnd_5045137 := by
    simpa [prefixWord, tailWord_5045137, baseEnd_5045137] using wordTrace_append hprefix tailTrace_5045137
  have hstable : (prefixWord ++ tailWord_5045137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045137).length < 2 ^ (prefixWord ++ tailWord_5045137).sum := by decide
  have hdescent : baseEnd_5045137 < baseStart_5045137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045142 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5045142 : Nat := 118140960795 + 5045142 * 2 ^ 59
def prefixEnd_5045142 : Nat := 4983230072969 + 3 ^ 40 * 5045142 * 2
def baseEnd_5045142 : Nat := 2590582816185805092422821

theorem tailTrace_5045142 : CollatzResearch.WordTrace tailWord_5045142 prefixEnd_5045142 2590582816185805092422821 := by
  unfold tailWord_5045142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11500715368019978156244605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122674297258879766999942453 11500715368019978156244605)
  ·
    refine ⟨4312768263007491808591727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11500715368019978156244605 4312768263007491808591727)
    ·
      refine ⟨6469152394511237712887591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312768263007491808591727 6469152394511237712887591)
      ·
        refine ⟨9703728591766856569331387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6469152394511237712887591 9703728591766856569331387)
        ·
          refine ⟨14555592887650284853997081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9703728591766856569331387 14555592887650284853997081)
          ·
            refine ⟨10916694665737713640497811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14555592887650284853997081 10916694665737713640497811)
            ·
              refine ⟨16375041998606570460746717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10916694665737713640497811 16375041998606570460746717)
              ·
                refine ⟨6140640749477463922780019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16375041998606570460746717 6140640749477463922780019)
                ·
                  refine ⟨9210961124216195884170029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140640749477463922780019 9210961124216195884170029)
                  ·
                    refine ⟨3454110421581073456563761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9210961124216195884170029 3454110421581073456563761)
                    ·
                      refine ⟨2590582816185805092422821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454110421581073456563761 2590582816185805092422821)
                      ·
                        rfl

theorem cell23_5045142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5045142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045142 prefixEnd_5045142 := by exact prefixLift 5045142
  have htrace : WordTrace (prefixWord ++ tailWord_5045142) baseStart_5045142 baseEnd_5045142 := by
    simpa [prefixWord, tailWord_5045142, baseEnd_5045142] using wordTrace_append hprefix tailTrace_5045142
  have hstable : (prefixWord ++ tailWord_5045142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045142).length < 2 ^ (prefixWord ++ tailWord_5045142).sum := by decide
  have hdescent : baseEnd_5045142 < baseStart_5045142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045194 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5045194 : Nat := 118140960795 + 5045194 * 2 ^ 59
def prefixEnd_5045194 : Nat := 4983230072969 + 3 ^ 40 * 5045194 * 2
def baseEnd_5045194 : Nat := 2590609517179838888972581

theorem tailTrace_5045194 : CollatzResearch.WordTrace tailWord_5045194 prefixEnd_5045194 2590609517179838888972581 := by
  unfold tailWord_5045194
  simp only [CollatzResearch.WordTrace]
  refine ⟨46003335621032815845201659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122675561656087508920537757 46003335621032815845201659)
  ·
    refine ⟨69005003431549223767802489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46003335621032815845201659 69005003431549223767802489)
    ·
      refine ⟨51753752573661917825851867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69005003431549223767802489 51753752573661917825851867)
      ·
        refine ⟨77630628860492876738777801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51753752573661917825851867 77630628860492876738777801)
        ·
          refine ⟨58222971645369657554083351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77630628860492876738777801 58222971645369657554083351)
          ·
            refine ⟨87334457468054486331125027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58222971645369657554083351 87334457468054486331125027)
            ·
              refine ⟨131001686202081729496687541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87334457468054486331125027 131001686202081729496687541)
              ·
                refine ⟨12281408081445162140314457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131001686202081729496687541 12281408081445162140314457)
                ·
                  refine ⟨9211056061083871605235843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12281408081445162140314457 9211056061083871605235843)
                  ·
                    refine ⟨13816584091625807407853765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9211056061083871605235843 13816584091625807407853765)
                    ·
                      refine ⟨2590609517179838888972581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13816584091625807407853765 2590609517179838888972581)
                      ·
                        rfl

theorem cell23_5045194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5045194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045194 prefixEnd_5045194 := by exact prefixLift 5045194
  have htrace : WordTrace (prefixWord ++ tailWord_5045194) baseStart_5045194 baseEnd_5045194 := by
    simpa [prefixWord, tailWord_5045194, baseEnd_5045194] using wordTrace_append hprefix tailTrace_5045194
  have hstable : (prefixWord ++ tailWord_5045194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045194).length < 2 ^ (prefixWord ++ tailWord_5045194).sum := by decide
  have hdescent : baseEnd_5045194 < baseStart_5045194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045207 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_5045207 : Nat := 118140960795 + 5045207 * 2 ^ 59
def prefixEnd_5045207 : Nat := 4983230072969 + 3 ^ 40 * 5045207 * 2
def baseEnd_5045207 : Nat := 2590616192428347338110021

theorem tailTrace_5045207 : CollatzResearch.WordTrace tailWord_5045207 prefixEnd_5045207 2590616192428347338110021 := by
  unfold tailWord_5045207
  simp only [CollatzResearch.WordTrace]
  refine ⟨184013816633084166601029875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122675877755389444400686583 184013816633084166601029875)
  ·
    refine ⟨276020724949626249901544813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184013816633084166601029875 276020724949626249901544813)
    ·
      refine ⟨103507771856109843713079305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276020724949626249901544813 103507771856109843713079305)
      ·
        refine ⟨77630828892082382784809479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103507771856109843713079305 77630828892082382784809479)
        ·
          refine ⟨116446243338123574177214219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77630828892082382784809479 116446243338123574177214219)
          ·
            refine ⟨174669365007185361265821329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116446243338123574177214219 174669365007185361265821329)
            ·
              refine ⟨131002023755389020949365997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174669365007185361265821329 131002023755389020949365997)
              ·
                refine ⟨49125758908270882856012249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131002023755389020949365997 49125758908270882856012249)
                ·
                  refine ⟨36844319181203162142009187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49125758908270882856012249 36844319181203162142009187)
                  ·
                    refine ⟨55266478771804743213013781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36844319181203162142009187 55266478771804743213013781)
                    ·
                      refine ⟨2590616192428347338110021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55266478771804743213013781 2590616192428347338110021)
                      ·
                        rfl

theorem cell23_5045207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_5045207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045207 prefixEnd_5045207 := by exact prefixLift 5045207
  have htrace : WordTrace (prefixWord ++ tailWord_5045207) baseStart_5045207 baseEnd_5045207 := by
    simpa [prefixWord, tailWord_5045207, baseEnd_5045207] using wordTrace_append hprefix tailTrace_5045207
  have hstable : (prefixWord ++ tailWord_5045207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045207).length < 2 ^ (prefixWord ++ tailWord_5045207).sum := by decide
  have hdescent : baseEnd_5045207 < baseStart_5045207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045257 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_5045257 : Nat := 118140960795 + 5045257 * 2 ^ 59
def prefixEnd_5045257 : Nat := 4983230072969 + 3 ^ 40 * 5045257 * 2
def baseEnd_5045257 : Nat := 2590641866461072142484791

theorem tailTrace_5045257 : CollatzResearch.WordTrace tailWord_5045257 prefixEnd_5045257 2590641866461072142484791 := by
  unfold tailWord_5045257
  simp only [CollatzResearch.WordTrace]
  refine ⟨184015640282903025140350025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122677093521935350093566683 184015640282903025140350025)
  ·
    refine ⟨138011730212177268855262519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184015640282903025140350025 138011730212177268855262519)
    ·
      refine ⟨207017595318265903282893779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138011730212177268855262519 207017595318265903282893779)
      ·
        refine ⟨310526392977398854924340669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207017595318265903282893779 310526392977398854924340669)
        ·
          refine ⟨116447397366524570596627751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310526392977398854924340669 116447397366524570596627751)
          ·
            refine ⟨174671096049786855894941627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116447397366524570596627751 174671096049786855894941627)
            ·
              refine ⟨262006644074680283842412441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174671096049786855894941627 262006644074680283842412441)
              ·
                refine ⟨196504983056010212881809331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262006644074680283842412441 196504983056010212881809331)
                ·
                  refine ⟨294757474584015319322713997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196504983056010212881809331 294757474584015319322713997)
                  ·
                    refine ⟨110534052969005744746017749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294757474584015319322713997 110534052969005744746017749)
                    ·
                      refine ⟨2590641866461072142484791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110534052969005744746017749 2590641866461072142484791)
                      ·
                        rfl

theorem cell23_5045257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_5045257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045257 prefixEnd_5045257 := by exact prefixLift 5045257
  have htrace : WordTrace (prefixWord ++ tailWord_5045257) baseStart_5045257 baseEnd_5045257 := by
    simpa [prefixWord, tailWord_5045257, baseEnd_5045257] using wordTrace_append hprefix tailTrace_5045257
  have hstable : (prefixWord ++ tailWord_5045257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045257).length < 2 ^ (prefixWord ++ tailWord_5045257).sum := by decide
  have hdescent : baseEnd_5045257 < baseStart_5045257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045301 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_5045301 : Nat := 118140960795 + 5045301 * 2 ^ 59
def prefixEnd_5045301 : Nat := 4983230072969 + 3 ^ 40 * 5045301 * 2
def baseEnd_5045301 : Nat := 2590664459609869970334589

theorem tailTrace_5045301 : CollatzResearch.WordTrace tailWord_5045301 prefixEnd_5045301 2590664459609869970334589 := by
  unfold tailWord_5045301
  simp only [CollatzResearch.WordTrace]
  refine ⟨184017245094743620654951757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122678163396495747103301171 184017245094743620654951757)
  ·
    refine ⟨69006466910528857745606909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184017245094743620654951757 69006466910528857745606909)
    ·
      refine ⟨25877425091448321654602591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69006466910528857745606909 25877425091448321654602591)
      ·
        refine ⟨38816137637172482481903887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25877425091448321654602591 38816137637172482481903887)
        ·
          refine ⟨58224206455758723722855831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38816137637172482481903887 58224206455758723722855831)
          ·
            refine ⟨87336309683638085584283747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58224206455758723722855831 87336309683638085584283747)
            ·
              refine ⟨131004464525457128376425621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87336309683638085584283747 131004464525457128376425621)
              ·
                refine ⟨6140834274630802892644951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131004464525457128376425621 6140834274630802892644951)
                ·
                  refine ⟨9211251411946204338967427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140834274630802892644951 9211251411946204338967427)
                  ·
                    refine ⟨13816877117919306508451141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9211251411946204338967427 13816877117919306508451141)
                    ·
                      refine ⟨2590664459609869970334589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13816877117919306508451141 2590664459609869970334589)
                      ·
                        rfl

theorem cell23_5045301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_5045301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045301 prefixEnd_5045301 := by exact prefixLift 5045301
  have htrace : WordTrace (prefixWord ++ tailWord_5045301) baseStart_5045301 baseEnd_5045301 := by
    simpa [prefixWord, tailWord_5045301, baseEnd_5045301] using wordTrace_append hprefix tailTrace_5045301
  have hstable : (prefixWord ++ tailWord_5045301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045301).length < 2 ^ (prefixWord ++ tailWord_5045301).sum := by decide
  have hdescent : baseEnd_5045301 < baseStart_5045301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045305 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5045305 : Nat := 118140960795 + 5045305 * 2 ^ 59
def prefixEnd_5045305 : Nat := 4983230072969 + 3 ^ 40 * 5045305 * 2
def baseEnd_5045305 : Nat := 2590666513532487954684571

theorem tailTrace_5045305 : CollatzResearch.WordTrace tailWord_5045305 prefixEnd_5045305 2590666513532487954684571 := by
  unfold tailWord_5045305
  simp only [CollatzResearch.WordTrace]
  refine ⟨184017390986729129338097369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122678260657819419558731579 184017390986729129338097369)
  ·
    refine ⟨138013043240046847003573027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184017390986729129338097369 138013043240046847003573027)
    ·
      refine ⟨207019564860070270505359541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138013043240046847003573027 207019564860070270505359541)
      ·
        refine ⟨19408084205631587859877457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207019564860070270505359541 19408084205631587859877457)
        ·
          refine ⟨14556063154223690894908093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19408084205631587859877457 14556063154223690894908093)
          ·
            refine ⟨5458523682833884085590535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14556063154223690894908093 5458523682833884085590535)
            ·
              refine ⟨8187785524250826128385803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458523682833884085590535 8187785524250826128385803)
              ·
                refine ⟨12281678286376239192578705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8187785524250826128385803 12281678286376239192578705)
                ·
                  refine ⟨9211258714782179394434029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12281678286376239192578705 9211258714782179394434029)
                  ·
                    refine ⟨3454222018043317272912761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9211258714782179394434029 3454222018043317272912761)
                    ·
                      refine ⟨2590666513532487954684571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454222018043317272912761 2590666513532487954684571)
                      ·
                        rfl

theorem cell23_5045305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5045305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045305 prefixEnd_5045305 := by exact prefixLift 5045305
  have htrace : WordTrace (prefixWord ++ tailWord_5045305) baseStart_5045305 baseEnd_5045305 := by
    simpa [prefixWord, tailWord_5045305, baseEnd_5045305] using wordTrace_append hprefix tailTrace_5045305
  have hstable : (prefixWord ++ tailWord_5045305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045305).length < 2 ^ (prefixWord ++ tailWord_5045305).sum := by decide
  have hdescent : baseEnd_5045305 < baseStart_5045305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045358 : List Nat := [4, 1, 2, 2, 1, 4, 2, 7]
def baseStart_5045358 : Nat := 118140960795 + 5045358 * 2 ^ 59
def prefixEnd_5045358 : Nat := 4983230072969 + 3 ^ 40 * 5045358 * 2
def baseEnd_5045358 : Nat := 95951619555821342493401

theorem tailTrace_5045358 : CollatzResearch.WordTrace tailWord_5045358 prefixEnd_5045358 95951619555821342493401 := by
  unfold tailWord_5045358
  simp only [CollatzResearch.WordTrace]
  refine ⟨23002415506942139923722091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122679549370358079593184485 23002415506942139923722091)
  ·
    refine ⟨34503623260413209885583137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23002415506942139923722091 34503623260413209885583137)
    ·
      refine ⟨25877717445309907414187353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34503623260413209885583137 25877717445309907414187353)
      ·
        refine ⟨19408288083982430560640515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25877717445309907414187353 19408288083982430560640515)
        ·
          refine ⟨29112432125973645840960773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19408288083982430560640515 29112432125973645840960773)
          ·
            refine ⟨5458581023620058595180145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29112432125973645840960773 5458581023620058595180145)
            ·
              refine ⟨4093935767715043946385109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458581023620058595180145 4093935767715043946385109)
              ·
                refine ⟨95951619555821342493401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4093935767715043946385109 95951619555821342493401)
                ·
                  rfl

theorem cell23_5045358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_5045358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045358 prefixEnd_5045358 := by exact prefixLift 5045358
  have htrace : WordTrace (prefixWord ++ tailWord_5045358) baseStart_5045358 baseEnd_5045358 := by
    simpa [prefixWord, tailWord_5045358, baseEnd_5045358] using wordTrace_append hprefix tailTrace_5045358
  have hstable : (prefixWord ++ tailWord_5045358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045358).length < 2 ^ (prefixWord ++ tailWord_5045358).sum := by decide
  have hdescent : baseEnd_5045358 < baseStart_5045358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045369 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 1, 2, 2]
def baseStart_5045369 : Nat := 118140960795 + 5045369 * 2 ^ 59
def prefixEnd_5045369 : Nat := 4983230072969 + 3 ^ 40 * 5045369 * 2
def baseEnd_5045369 : Nat := 2590699376294375704284277

theorem tailTrace_5045369 : CollatzResearch.WordTrace tailWord_5045369 prefixEnd_5045369 2590699376294375704284277 := by
  unfold tailWord_5045369
  simp only [CollatzResearch.WordTrace]
  refine ⟨184019725258497268268427161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122679816838998178845618107 184019725258497268268427161)
  ·
    refine ⟨138014793943872951201320371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184019725258497268268427161 138014793943872951201320371)
    ·
      refine ⟨207022190915809426801980557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138014793943872951201320371 207022190915809426801980557)
      ·
        refine ⟨77633321593428535050742709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207022190915809426801980557 77633321593428535050742709)
        ·
          refine ⟨7278123899383925161007129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77633321593428535050742709 7278123899383925161007129)
          ·
            refine ⟨5458592924537943870755347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7278123899383925161007129 5458592924537943870755347)
            ·
              refine ⟨8187889386806915806133021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458592924537943870755347 8187889386806915806133021)
              ·
                refine ⟨3070458520052593427299883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8187889386806915806133021 3070458520052593427299883)
                ·
                  refine ⟨4605687780078890140949825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070458520052593427299883 4605687780078890140949825)
                  ·
                    refine ⟨3454265835059167605712369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4605687780078890140949825 3454265835059167605712369)
                    ·
                      refine ⟨2590699376294375704284277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454265835059167605712369 2590699376294375704284277)
                      ·
                        rfl

theorem cell23_5045369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_5045369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045369 prefixEnd_5045369 := by exact prefixLift 5045369
  have htrace : WordTrace (prefixWord ++ tailWord_5045369) baseStart_5045369 baseEnd_5045369 := by
    simpa [prefixWord, tailWord_5045369, baseEnd_5045369] using wordTrace_append hprefix tailTrace_5045369
  have hstable : (prefixWord ++ tailWord_5045369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045369).length < 2 ^ (prefixWord ++ tailWord_5045369).sum := by decide
  have hdescent : baseEnd_5045369 < baseStart_5045369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045402 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5045402 : Nat := 118140960795 + 5045402 * 2 ^ 59
def prefixEnd_5045402 : Nat := 4983230072969 + 3 ^ 40 * 5045402 * 2
def baseEnd_5045402 : Nat := 2590716321155974075171625

theorem tailTrace_5045402 : CollatzResearch.WordTrace tailWord_5045402 prefixEnd_5045402 2590716321155974075171625 := by
  unfold tailWord_5045402
  simp only [CollatzResearch.WordTrace]
  refine ⟨46005232216844428726094615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122680619244918476602918973 46005232216844428726094615)
  ·
    refine ⟨69007848325266643089141923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46005232216844428726094615 69007848325266643089141923)
    ·
      refine ⟨103511772487899964633712885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69007848325266643089141923 103511772487899964633712885)
      ·
        refine ⟨9704228670740621684410583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103511772487899964633712885 9704228670740621684410583)
        ·
          refine ⟨14556343006110932526615875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704228670740621684410583 14556343006110932526615875)
          ·
            refine ⟨21834514509166398789923813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14556343006110932526615875 21834514509166398789923813)
            ·
              refine ⟨4093971470468699773110715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21834514509166398789923813 4093971470468699773110715)
              ·
                refine ⟨6140957205703049659666073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093971470468699773110715 6140957205703049659666073)
                ·
                  refine ⟨4605717904277287244749555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6140957205703049659666073 4605717904277287244749555)
                  ·
                    refine ⟨6908576856415930867124333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4605717904277287244749555 6908576856415930867124333)
                    ·
                      refine ⟨2590716321155974075171625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908576856415930867124333 2590716321155974075171625)
                      ·
                        rfl

theorem cell23_5045402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5045402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045402 prefixEnd_5045402 := by exact prefixLift 5045402
  have htrace : WordTrace (prefixWord ++ tailWord_5045402) baseStart_5045402 baseEnd_5045402 := by
    simpa [prefixWord, tailWord_5045402, baseEnd_5045402] using wordTrace_append hprefix tailTrace_5045402
  have hstable : (prefixWord ++ tailWord_5045402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045402).length < 2 ^ (prefixWord ++ tailWord_5045402).sum := by decide
  have hdescent : baseEnd_5045402 < baseStart_5045402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045408 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2]
def baseStart_5045408 : Nat := 118140960795 + 5045408 * 2 ^ 59
def prefixEnd_5045408 : Nat := 4983230072969 + 3 ^ 40 * 5045408 * 2
def baseEnd_5045408 : Nat := 2590719402039901051696597

theorem tailTrace_5045408 : CollatzResearch.WordTrace tailWord_5045408 prefixEnd_5045408 2590719402039901051696597 := by
  unfold tailWord_5045408
  simp only [CollatzResearch.WordTrace]
  refine ⟨92010573852677988964548439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122680765136903985286064585 92010573852677988964548439)
  ·
    refine ⟨138015860779016983446822659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92010573852677988964548439 138015860779016983446822659)
    ·
      refine ⟨207023791168525475170233989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138015860779016983446822659 207023791168525475170233989)
      ·
        refine ⟨38816960844098526594418873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207023791168525475170233989 38816960844098526594418873)
        ·
          refine ⟨29112720633073894945814155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38816960844098526594418873 29112720633073894945814155)
          ·
            refine ⟨43669080949610842418721233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29112720633073894945814155 43669080949610842418721233)
            ·
              refine ⟨32751810712208131814040925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43669080949610842418721233 32751810712208131814040925)
              ·
                refine ⟨12281929017078049430265347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32751810712208131814040925 12281929017078049430265347)
                ·
                  refine ⟨18422893525617074145398021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12281929017078049430265347 18422893525617074145398021)
                  ·
                    refine ⟨3454292536053201402262129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18422893525617074145398021 3454292536053201402262129)
                    ·
                      refine ⟨2590719402039901051696597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454292536053201402262129 2590719402039901051696597)
                      ·
                        rfl

theorem cell23_5045408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_5045408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045408 prefixEnd_5045408 := by exact prefixLift 5045408
  have htrace : WordTrace (prefixWord ++ tailWord_5045408) baseStart_5045408 baseEnd_5045408 := by
    simpa [prefixWord, tailWord_5045408, baseEnd_5045408] using wordTrace_append hprefix tailTrace_5045408
  have hstable : (prefixWord ++ tailWord_5045408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045408).length < 2 ^ (prefixWord ++ tailWord_5045408).sum := by decide
  have hdescent : baseEnd_5045408 < baseStart_5045408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045412 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_5045412 : Nat := 118140960795 + 5045412 * 2 ^ 59
def prefixEnd_5045412 : Nat := 4983230072969 + 3 ^ 40 * 5045412 * 2
def baseEnd_5045412 : Nat := 2590721455962519036046579

theorem tailTrace_5045412 : CollatzResearch.WordTrace tailWord_5045412 prefixEnd_5045412 2590721455962519036046579 := by
  unfold tailWord_5045412
  simp only [CollatzResearch.WordTrace]
  refine ⟨92010646798670743306121245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122680862398227657741494993 92010646798670743306121245)
  ·
    refine ⟨34503992549501528739795467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92010646798670743306121245 34503992549501528739795467)
    ·
      refine ⟨51755988824252293109693201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34503992549501528739795467 51755988824252293109693201)
      ·
        refine ⟨38816991618189219832269901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51755988824252293109693201 38816991618189219832269901)
        ·
          refine ⟨14556371856820957437101213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38816991618189219832269901 14556371856820957437101213)
          ·
            refine ⟨5458639446307859038912955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14556371856820957437101213 5458639446307859038912955)
            ·
              refine ⟨8187959169461788558369433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458639446307859038912955 8187959169461788558369433)
              ·
                refine ⟨6140969377096341418777075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8187959169461788558369433 6140969377096341418777075)
                ·
                  refine ⟨9211454065644512128165613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6140969377096341418777075 9211454065644512128165613)
                  ·
                    refine ⟨3454295274616692048062105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9211454065644512128165613 3454295274616692048062105)
                    ·
                      refine ⟨2590721455962519036046579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454295274616692048062105 2590721455962519036046579)
                      ·
                        rfl

theorem cell23_5045412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_5045412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045412 prefixEnd_5045412 := by exact prefixLift 5045412
  have htrace : WordTrace (prefixWord ++ tailWord_5045412) baseStart_5045412 baseEnd_5045412 := by
    simpa [prefixWord, tailWord_5045412, baseEnd_5045412] using wordTrace_append hprefix tailTrace_5045412
  have hstable : (prefixWord ++ tailWord_5045412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045412).length < 2 ^ (prefixWord ++ tailWord_5045412).sum := by decide
  have hdescent : baseEnd_5045412 < baseStart_5045412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045425 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5045425 : Nat := 118140960795 + 5045425 * 2 ^ 59
def prefixEnd_5045425 : Nat := 4983230072969 + 3 ^ 40 * 5045425 * 2
def baseEnd_5045425 : Nat := 2590728131211027485184019

theorem tailTrace_5045425 : CollatzResearch.WordTrace tailWord_5045425 prefixEnd_5045425 2590728131211027485184019 := by
  unfold tailWord_5045425
  simp only [CollatzResearch.WordTrace]
  refine ⟨184021767746294389832465729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122681178497529593221643819 184021767746294389832465729)
  ·
    refine ⟨138016325809720792374349297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184021767746294389832465729 138016325809720792374349297)
    ·
      refine ⟨103512244357290594280761973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138016325809720792374349297 103512244357290594280761973)
      ·
        refine ⟨9704272908495993213821435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103512244357290594280761973 9704272908495993213821435)
        ·
          refine ⟨14556409362743989820732153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704272908495993213821435 14556409362743989820732153)
          ·
            refine ⟨10917307022057992365549115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14556409362743989820732153 10917307022057992365549115)
            ·
              refine ⟨16375960533086988548323673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10917307022057992365549115 16375960533086988548323673)
              ·
                refine ⟨12281970399815241411242755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16375960533086988548323673 12281970399815241411242755)
                ·
                  refine ⟨18422955599722862116864133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12281970399815241411242755 18422955599722862116864133)
                  ·
                    refine ⟨3454304174948036646912025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18422955599722862116864133 3454304174948036646912025)
                    ·
                      refine ⟨2590728131211027485184019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454304174948036646912025 2590728131211027485184019)
                      ·
                        rfl

theorem cell23_5045425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5045425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045425 prefixEnd_5045425 := by exact prefixLift 5045425
  have htrace : WordTrace (prefixWord ++ tailWord_5045425) baseStart_5045425 baseEnd_5045425 := by
    simpa [prefixWord, tailWord_5045425, baseEnd_5045425] using wordTrace_append hprefix tailTrace_5045425
  have hstable : (prefixWord ++ tailWord_5045425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045425).length < 2 ^ (prefixWord ++ tailWord_5045425).sum := by decide
  have hdescent : baseEnd_5045425 < baseStart_5045425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045458 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5045458 : Nat := 118140960795 + 5045458 * 2 ^ 59
def prefixEnd_5045458 : Nat := 4983230072969 + 3 ^ 40 * 5045458 * 2
def baseEnd_5045458 : Nat := 2590745076072625856071367

theorem tailTrace_5045458 : CollatzResearch.WordTrace tailWord_5045458 prefixEnd_5045458 2590745076072625856071367 := by
  unfold tailWord_5045458
  simp only [CollatzResearch.WordTrace]
  refine ⟨46005742838793709117104257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122681980903449890978944685 46005742838793709117104257)
  ·
    refine ⟨34504307129095281837828193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46005742838793709117104257 34504307129095281837828193)
    ·
      refine ⟨25878230346821461378371145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34504307129095281837828193 25878230346821461378371145)
      ·
        refine ⟨19408672760116096033778359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25878230346821461378371145 19408672760116096033778359)
        ·
          refine ⟨29113009140174144050667539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19408672760116096033778359 29113009140174144050667539)
          ·
            refine ⟨43669513710261216076001309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29113009140174144050667539 43669513710261216076001309)
            ·
              refine ⟨16376067641347956028500491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43669513710261216076001309 16376067641347956028500491)
              ·
                refine ⟨24564101462021934042750737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16376067641347956028500491 24564101462021934042750737)
                ·
                  refine ⟨18423076096516450532063053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24564101462021934042750737 18423076096516450532063053)
                  ·
                    refine ⟨6908653536193668949523645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18423076096516450532063053 6908653536193668949523645)
                    ·
                      refine ⟨2590745076072625856071367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908653536193668949523645 2590745076072625856071367)
                      ·
                        rfl

theorem cell23_5045458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5045458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045458 prefixEnd_5045458 := by exact prefixLift 5045458
  have htrace : WordTrace (prefixWord ++ tailWord_5045458) baseStart_5045458 baseEnd_5045458 := by
    simpa [prefixWord, tailWord_5045458, baseEnd_5045458] using wordTrace_append hprefix tailTrace_5045458
  have hstable : (prefixWord ++ tailWord_5045458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045458).length < 2 ^ (prefixWord ++ tailWord_5045458).sum := by decide
  have hdescent : baseEnd_5045458 < baseStart_5045458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045498 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_5045498 : Nat := 118140960795 + 5045498 * 2 ^ 59
def prefixEnd_5045498 : Nat := 4983230072969 + 3 ^ 40 * 5045498 * 2
def baseEnd_5045498 : Nat := 2590765615298805699571183

theorem tailTrace_5045498 : CollatzResearch.WordTrace tailWord_5045498 prefixEnd_5045498 2590765615298805699571183 := by
  unfold tailWord_5045498
  simp only [CollatzResearch.WordTrace]
  refine ⟨46006107568757480824968287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122682953516686615533248765 46006107568757480824968287)
  ·
    refine ⟨69009161353136221237452431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46006107568757480824968287 69009161353136221237452431)
    ·
      refine ⟨103513742029704331856178647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69009161353136221237452431 103513742029704331856178647)
      ·
        refine ⟨155270613044556497784267971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103513742029704331856178647 155270613044556497784267971)
        ·
          refine ⟨232905919566834746676401957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155270613044556497784267971 232905919566834746676401957)
          ·
            refine ⟨43669859918781515001825367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232905919566834746676401957 43669859918781515001825367)
            ·
              refine ⟨65504789878172272502738051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43669859918781515001825367 65504789878172272502738051)
              ·
                refine ⟨98257184817258408754107077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65504789878172272502738051 98257184817258408754107077)
                ·
                  refine ⟨18423222153235951641395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98257184817258408754107077 18423222153235951641395077)
                  ·
                    refine ⟨3454354153731740932761577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18423222153235951641395077 3454354153731740932761577)
                    ·
                      refine ⟨2590765615298805699571183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454354153731740932761577 2590765615298805699571183)
                      ·
                        rfl

theorem cell23_5045498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_5045498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045498 prefixEnd_5045498 := by exact prefixLift 5045498
  have htrace : WordTrace (prefixWord ++ tailWord_5045498) baseStart_5045498 baseEnd_5045498 := by
    simpa [prefixWord, tailWord_5045498, baseEnd_5045498] using wordTrace_append hprefix tailTrace_5045498
  have hstable : (prefixWord ++ tailWord_5045498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045498).length < 2 ^ (prefixWord ++ tailWord_5045498).sum := by decide
  have hdescent : baseEnd_5045498 < baseStart_5045498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045518 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_5045518 : Nat := 118140960795 + 5045518 * 2 ^ 59
def prefixEnd_5045518 : Nat := 4983230072969 + 3 ^ 40 * 5045518 * 2
def baseEnd_5045518 : Nat := 2590775884911895621321091

theorem tailTrace_5045518 : CollatzResearch.WordTrace tailWord_5045518 prefixEnd_5045518 2590775884911895621321091 := by
  unfold tailWord_5045518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23003144966869683339450151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122683439823304977810400805 23003144966869683339450151)
  ·
    refine ⟨34504717450304525009175227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23003144966869683339450151 34504717450304525009175227)
    ·
      refine ⟨51757076175456787513762841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34504717450304525009175227 51757076175456787513762841)
      ·
        refine ⟨38817807131592590635322131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51757076175456787513762841 38817807131592590635322131)
        ·
          refine ⟨58226710697388885952983197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38817807131592590635322131 58226710697388885952983197)
          ·
            refine ⟨21835016511520832232368699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58226710697388885952983197 21835016511520832232368699)
            ·
              refine ⟨32752524767281248348553049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21835016511520832232368699 32752524767281248348553049)
              ·
                refine ⟨24564393575460936261414787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32752524767281248348553049 24564393575460936261414787)
                ·
                  refine ⟨36846590363191404392122181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24564393575460936261414787 36846590363191404392122181)
                  ·
                    refine ⟨6908735693098388323522909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36846590363191404392122181 6908735693098388323522909)
                    ·
                      refine ⟨2590775884911895621321091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908735693098388323522909 2590775884911895621321091)
                      ·
                        rfl

theorem cell23_5045518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_5045518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045518 prefixEnd_5045518 := by exact prefixLift 5045518
  have htrace : WordTrace (prefixWord ++ tailWord_5045518) baseStart_5045518 baseEnd_5045518 := by
    simpa [prefixWord, tailWord_5045518, baseEnd_5045518] using wordTrace_append hprefix tailTrace_5045518
  have hstable : (prefixWord ++ tailWord_5045518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045518).length < 2 ^ (prefixWord ++ tailWord_5045518).sum := by decide
  have hdescent : baseEnd_5045518 < baseStart_5045518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045531 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3]
def baseStart_5045531 : Nat := 118140960795 + 5045531 * 2 ^ 59
def prefixEnd_5045531 : Nat := 4983230072969 + 3 ^ 40 * 5045531 * 2
def baseEnd_5045531 : Nat := 2590782560160404070458531

theorem tailTrace_5045531 : CollatzResearch.WordTrace tailWord_5045531 prefixEnd_5045531 2590782560160404070458531 := by
  unfold tailWord_5045531
  simp only [CollatzResearch.WordTrace]
  refine ⟨184025633883910369935824447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122683755922606913290549631 184025633883910369935824447)
  ·
    refine ⟨276038450825865554903736671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184025633883910369935824447 276038450825865554903736671)
    ·
      refine ⟨414057676238798332355605007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276038450825865554903736671 414057676238798332355605007)
      ·
        refine ⟨621086514358197498533407511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414057676238798332355605007 621086514358197498533407511)
        ·
          refine ⟨931629771537296247800111267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621086514358197498533407511 931629771537296247800111267)
          ·
            refine ⟨1397444657305944371700166901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931629771537296247800111267 1397444657305944371700166901)
            ·
              refine ⟨131010436622432284846890647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1397444657305944371700166901 131010436622432284846890647)
              ·
                refine ⟨196515654933648427270335971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131010436622432284846890647 196515654933648427270335971)
                ·
                  refine ⟨294773482400472640905503957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196515654933648427270335971 294773482400472640905503957)
                  ·
                    refine ⟨6908753493761077521222749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 294773482400472640905503957 6908753493761077521222749)
                    ·
                      refine ⟨2590782560160404070458531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908753493761077521222749 2590782560160404070458531)
                      ·
                        rfl

theorem cell23_5045531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3].length) (baseStart_5045531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045531 prefixEnd_5045531 := by exact prefixLift 5045531
  have htrace : WordTrace (prefixWord ++ tailWord_5045531) baseStart_5045531 baseEnd_5045531 := by
    simpa [prefixWord, tailWord_5045531, baseEnd_5045531] using wordTrace_append hprefix tailTrace_5045531
  have hstable : (prefixWord ++ tailWord_5045531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045531).length < 2 ^ (prefixWord ++ tailWord_5045531).sum := by decide
  have hdescent : baseEnd_5045531 < baseStart_5045531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045551 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 5, 5]
def baseStart_5045551 : Nat := 118140960795 + 5045551 * 2 ^ 59
def prefixEnd_5045551 : Nat := 4983230072969 + 3 ^ 40 * 5045551 * 2
def baseEnd_5045551 : Nat := 863597609924497997402813

theorem tailTrace_5045551 : CollatzResearch.WordTrace tailWord_5045551 prefixEnd_5045551 863597609924497997402813 := by
  unfold tailWord_5045551
  simp only [CollatzResearch.WordTrace]
  refine ⟨184026363343837913351552507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122684242229225275567701671 184026363343837913351552507)
  ·
    refine ⟨276039545015756870027328761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184026363343837913351552507 276039545015756870027328761)
    ·
      refine ⟨207029658761817652520496571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276039545015756870027328761 207029658761817652520496571)
      ·
        refine ⟨310544488142726478780744857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207029658761817652520496571 310544488142726478780744857)
        ·
          refine ⟨232908366107044859085558643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310544488142726478780744857 232908366107044859085558643)
          ·
            refine ⟨349362549160567288628337965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232908366107044859085558643 349362549160567288628337965)
            ·
              refine ⟨131010955935212733235626737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349362549160567288628337965 131010955935212733235626737)
              ·
                refine ⟨98258216951409549926720053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131010955935212733235626737 98258216951409549926720053)
                ·
                  refine ⟨9211707839194645305630005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98258216951409549926720053 9211707839194645305630005)
                  ·
                    refine ⟨863597609924497997402813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9211707839194645305630005 863597609924497997402813)
                    ·
                      rfl

theorem cell23_5045551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_5045551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045551 prefixEnd_5045551 := by exact prefixLift 5045551
  have htrace : WordTrace (prefixWord ++ tailWord_5045551) baseStart_5045551 baseEnd_5045551 := by
    simpa [prefixWord, tailWord_5045551, baseEnd_5045551] using wordTrace_append hprefix tailTrace_5045551
  have hstable : (prefixWord ++ tailWord_5045551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045551).length < 2 ^ (prefixWord ++ tailWord_5045551).sum := by decide
  have hdescent : baseEnd_5045551 < baseStart_5045551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045571 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_5045571 : Nat := 118140960795 + 5045571 * 2 ^ 59
def prefixEnd_5045571 : Nat := 4983230072969 + 3 ^ 40 * 5045571 * 2
def baseEnd_5045571 : Nat := 2590803099386583913958347

theorem tailTrace_5045571 : CollatzResearch.WordTrace tailWord_5045571 prefixEnd_5045571 2590803099386583913958347 := by
  unfold tailWord_5045571
  simp only [CollatzResearch.WordTrace]
  refine ⟨184027092803765456767280567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122684728535843637844853711 184027092803765456767280567)
  ·
    refine ⟨276040639205648185150920851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184027092803765456767280567 276040639205648185150920851)
    ·
      refine ⟨414060958808472277726381277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276040639205648185150920851 414060958808472277726381277)
      ·
        refine ⟨155272859553177104147392979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414060958808472277726381277 155272859553177104147392979)
        ·
          refine ⟨232909289329765656221089469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155272859553177104147392979 232909289329765656221089469)
          ·
            refine ⟨87340983498662121082908551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232909289329765656221089469 87340983498662121082908551)
            ·
              refine ⟨131011475247993181624362827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87340983498662121082908551 131011475247993181624362827)
              ·
                refine ⟨196517212871989772436544241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131011475247993181624362827 196517212871989772436544241)
                ·
                  refine ⟨147387909653992329327408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196517212871989772436544241 147387909653992329327408181)
                  ·
                    refine ⟨13817616530061780874444517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147387909653992329327408181 13817616530061780874444517)
                    ·
                      refine ⟨2590803099386583913958347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13817616530061780874444517 2590803099386583913958347)
                      ·
                        rfl

theorem cell23_5045571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_5045571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045571 prefixEnd_5045571 := by exact prefixLift 5045571
  have htrace : WordTrace (prefixWord ++ tailWord_5045571) baseStart_5045571 baseEnd_5045571 := by
    simpa [prefixWord, tailWord_5045571, baseEnd_5045571] using wordTrace_append hprefix tailTrace_5045571
  have hstable : (prefixWord ++ tailWord_5045571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045571).length < 2 ^ (prefixWord ++ tailWord_5045571).sum := by decide
  have hdescent : baseEnd_5045571 < baseStart_5045571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045572 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 6]
def baseStart_5045572 : Nat := 118140960795 + 5045572 * 2 ^ 59
def prefixEnd_5045572 : Nat := 4983230072969 + 3 ^ 40 * 5045572 * 2
def baseEnd_5045572 : Nat := 287867068096359823338427

theorem tailTrace_5045572 : CollatzResearch.WordTrace tailWord_5045572 prefixEnd_5045572 287867068096359823338427 := by
  unfold tailWord_5045572
  simp only [CollatzResearch.WordTrace]
  refine ⟨92013564638380916969033485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122684752851174555958711313 92013564638380916969033485)
  ·
    refine ⟨34505086739392843863387557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92013564638380916969033485 34505086739392843863387557)
    ·
      refine ⟨6469703763636158224385167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34505086739392843863387557 6469703763636158224385167)
      ·
        refine ⟨9704555645454237336577751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6469703763636158224385167 9704555645454237336577751)
        ·
          refine ⟨14556833468181356004866627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704555645454237336577751 14556833468181356004866627)
          ·
            refine ⟨21835250202272034007299941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14556833468181356004866627 21835250202272034007299941)
            ·
              refine ⟨4094109412926006376368739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21835250202272034007299941 4094109412926006376368739)
              ·
                refine ⟨6141164119389009564553109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094109412926006376368739 6141164119389009564553109)
                ·
                  refine ⟨287867068096359823338427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6141164119389009564553109 287867068096359823338427)
                  ·
                    rfl

theorem cell23_5045572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_5045572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045572 prefixEnd_5045572 := by exact prefixLift 5045572
  have htrace : WordTrace (prefixWord ++ tailWord_5045572) baseStart_5045572 baseEnd_5045572 := by
    simpa [prefixWord, tailWord_5045572, baseEnd_5045572] using wordTrace_append hprefix tailTrace_5045572
  have hstable : (prefixWord ++ tailWord_5045572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045572).length < 2 ^ (prefixWord ++ tailWord_5045572).sum := by decide
  have hdescent : baseEnd_5045572 < baseStart_5045572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045602 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5045602 : Nat := 118140960795 + 5045602 * 2 ^ 59
def prefixEnd_5045602 : Nat := 4983230072969 + 3 ^ 40 * 5045602 * 2
def baseEnd_5045602 : Nat := 863606339095624430890235

theorem tailTrace_5045602 : CollatzResearch.WordTrace tailWord_5045602 prefixEnd_5045602 863606339095624430890235 := by
  unfold tailWord_5045602
  simp only [CollatzResearch.WordTrace]
  refine ⟨46007055866663287265414765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122685482311102099374439373 46007055866663287265414765)
  ·
    refine ⟨17252645949998732724530537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46007055866663287265414765 17252645949998732724530537)
    ·
      refine ⟨12939484462499049543397903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17252645949998732724530537 12939484462499049543397903)
      ·
        refine ⟨19409226693748574315096855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12939484462499049543397903 19409226693748574315096855)
        ·
          refine ⟨29113840040622861472645283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19409226693748574315096855 29113840040622861472645283)
          ·
            refine ⟨43670760060934292208967925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29113840040622861472645283 43670760060934292208967925)
            ·
              refine ⟨4094133755712589894590743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43670760060934292208967925 4094133755712589894590743)
              ·
                refine ⟨6141200633568884841886115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094133755712589894590743 6141200633568884841886115)
                ·
                  refine ⟨9211800950353327262829173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141200633568884841886115 9211800950353327262829173)
                  ·
                    refine ⟨863606339095624430890235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9211800950353327262829173 863606339095624430890235)
                    ·
                      rfl

theorem cell23_5045602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5045602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045602 prefixEnd_5045602 := by exact prefixLift 5045602
  have htrace : WordTrace (prefixWord ++ tailWord_5045602) baseStart_5045602 baseEnd_5045602 := by
    simpa [prefixWord, tailWord_5045602, baseEnd_5045602] using wordTrace_append hprefix tailTrace_5045602
  have hstable : (prefixWord ++ tailWord_5045602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045602).length < 2 ^ (prefixWord ++ tailWord_5045602).sum := by decide
  have hdescent : baseEnd_5045602 < baseStart_5045602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045615 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 2, 4]
def baseStart_5045615 : Nat := 118140960795 + 5045615 * 2 ^ 59
def prefixEnd_5045615 : Nat := 4983230072969 + 3 ^ 40 * 5045615 * 2
def baseEnd_5045615 : Nat := 863608564178460580602715

theorem tailTrace_5045615 : CollatzResearch.WordTrace tailWord_5045615 prefixEnd_5045615 863608564178460580602715 := by
  unfold tailWord_5045615
  simp only [CollatzResearch.WordTrace]
  refine ⟨184028697615606052281882299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122685798410404034854588199 184028697615606052281882299)
  ·
    refine ⟨276043046423409078422823449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184028697615606052281882299 276043046423409078422823449)
    ·
      refine ⟨207032284817556808817117587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276043046423409078422823449 207032284817556808817117587)
      ·
        refine ⟨310548427226335213225676381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207032284817556808817117587 310548427226335213225676381)
        ·
          refine ⟨116455660209875704959628643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310548427226335213225676381 116455660209875704959628643)
          ·
            refine ⟨174683490314813557439442965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116455660209875704959628643 174683490314813557439442965)
            ·
              refine ⟨8188288608506885504973889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174683490314813557439442965 8188288608506885504973889)
              ·
                refine ⟨6141216456380164128730417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8188288608506885504973889 6141216456380164128730417)
                ·
                  refine ⟨4605912342285123096547813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141216456380164128730417 4605912342285123096547813)
                  ·
                    refine ⟨863608564178460580602715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4605912342285123096547813 863608564178460580602715)
                    ·
                      rfl

theorem cell23_5045615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_5045615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045615 prefixEnd_5045615 := by exact prefixLift 5045615
  have htrace : WordTrace (prefixWord ++ tailWord_5045615) baseStart_5045615 baseEnd_5045615 := by
    simpa [prefixWord, tailWord_5045615, baseEnd_5045615] using wordTrace_append hprefix tailTrace_5045615
  have hstable : (prefixWord ++ tailWord_5045615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045615).length < 2 ^ (prefixWord ++ tailWord_5045615).sum := by decide
  have hdescent : baseEnd_5045615 < baseStart_5045615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045618 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5045618 : Nat := 118140960795 + 5045618 * 2 ^ 59
def prefixEnd_5045618 : Nat := 4983230072969 + 3 ^ 40 * 5045618 * 2
def baseEnd_5045618 : Nat := 2590827232977345230070631

theorem tailTrace_5045618 : CollatzResearch.WordTrace tailWord_5045618 prefixEnd_5045618 2590827232977345230070631 := by
  unfold tailWord_5045618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46007201758648795948560377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122685871356396789196161005 46007201758648795948560377)
  ·
    refine ⟨34505401318986596961420283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46007201758648795948560377 34505401318986596961420283)
    ·
      refine ⟨51758101978479895442130425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34505401318986596961420283 51758101978479895442130425)
      ·
        refine ⟨38818576483859921581597819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51758101978479895442130425 38818576483859921581597819)
        ·
          refine ⟨58227864725789882372396729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38818576483859921581597819 58227864725789882372396729)
          ·
            refine ⟨43670898544342411779297547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58227864725789882372396729 43670898544342411779297547)
            ·
              refine ⟨65506347816513617668946321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43670898544342411779297547 65506347816513617668946321)
              ·
                refine ⟨49129760862385213251709741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65506347816513617668946321 49129760862385213251709741)
                ·
                  refine ⟨18423660323394454969391153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49129760862385213251709741 18423660323394454969391153)
                  ·
                    refine ⟨13817745242545841227043365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18423660323394454969391153 13817745242545841227043365)
                    ·
                      refine ⟨2590827232977345230070631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13817745242545841227043365 2590827232977345230070631)
                      ·
                        rfl

theorem cell23_5045618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5045618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045618 prefixEnd_5045618 := by exact prefixLift 5045618
  have htrace : WordTrace (prefixWord ++ tailWord_5045618) baseStart_5045618 baseEnd_5045618 := by
    simpa [prefixWord, tailWord_5045618, baseEnd_5045618] using wordTrace_append hprefix tailTrace_5045618
  have hstable : (prefixWord ++ tailWord_5045618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045618).length < 2 ^ (prefixWord ++ tailWord_5045618).sum := by decide
  have hdescent : baseEnd_5045618 < baseStart_5045618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045635 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4]
def baseStart_5045635 : Nat := 118140960795 + 5045635 * 2 ^ 59
def prefixEnd_5045635 : Nat := 4983230072969 + 3 ^ 40 * 5045635 * 2
def baseEnd_5045635 : Nat := 2590835962148471663558053

theorem tailTrace_5045635 : CollatzResearch.WordTrace tailWord_5045635 prefixEnd_5045635 2590835962148471663558053 := by
  unfold tailWord_5045635
  simp only [CollatzResearch.WordTrace]
  refine ⟨184029427075533595697610359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122686284717022397131740239 184029427075533595697610359)
  ·
    refine ⟨276044140613300393546415539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184029427075533595697610359 276044140613300393546415539)
    ·
      refine ⟨414066210919950590319623309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276044140613300393546415539 414066210919950590319623309)
      ·
        refine ⟨155274829094981471369858741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414066210919950590319623309 155274829094981471369858741)
        ·
          refine ⟨14557015227654512940924257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155274829094981471369858741 14557015227654512940924257)
          ·
            refine ⟨10917761420740884705693193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14557015227654512940924257 10917761420740884705693193)
            ·
              refine ⟨8188321065555663529269895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10917761420740884705693193 8188321065555663529269895)
              ·
                refine ⟨12282481598333495293904843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188321065555663529269895 12282481598333495293904843)
                ·
                  refine ⟨18423722397500242940857265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12282481598333495293904843 18423722397500242940857265)
                  ·
                    refine ⟨13817791798125182205642949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18423722397500242940857265 13817791798125182205642949)
                    ·
                      refine ⟨2590835962148471663558053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13817791798125182205642949 2590835962148471663558053)
                      ·
                        rfl

theorem cell23_5045635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_5045635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045635 prefixEnd_5045635 := by exact prefixLift 5045635
  have htrace : WordTrace (prefixWord ++ tailWord_5045635) baseStart_5045635 baseEnd_5045635 := by
    simpa [prefixWord, tailWord_5045635, baseEnd_5045635] using wordTrace_append hprefix tailTrace_5045635
  have hstable : (prefixWord ++ tailWord_5045635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045635).length < 2 ^ (prefixWord ++ tailWord_5045635).sum := by decide
  have hdescent : baseEnd_5045635 < baseStart_5045635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045655 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_5045655 : Nat := 118140960795 + 5045655 * 2 ^ 59
def prefixEnd_5045655 : Nat := 4983230072969 + 3 ^ 40 * 5045655 * 2
def baseEnd_5045655 : Nat := 2590846231761561585307961

theorem tailTrace_5045655 : CollatzResearch.WordTrace tailWord_5045655 prefixEnd_5045655 2590846231761561585307961 := by
  unfold tailWord_5045655
  simp only [CollatzResearch.WordTrace]
  refine ⟨184030156535461139113338419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122686771023640759408892279 184030156535461139113338419)
  ·
    refine ⟨276045234803191708670007629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184030156535461139113338419 276045234803191708670007629)
    ·
      refine ⟨103516963051196890751252861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276045234803191708670007629 103516963051196890751252861)
      ·
        refine ⟨38818861144198834031719823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103516963051196890751252861 38818861144198834031719823)
        ·
          refine ⟨58228291716298251047579735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38818861144198834031719823 58228291716298251047579735)
          ·
            refine ⟨87342437574447376571369603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58228291716298251047579735 87342437574447376571369603)
            ·
              refine ⟨131013656361671064857054405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87342437574447376571369603 131013656361671064857054405)
              ·
                refine ⟨24565060567813324660697701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131013656361671064857054405 24565060567813324660697701)
                ·
                  refine ⟨4605948856464998373880819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24565060567813324660697701 4605948856464998373880819)
                  ·
                    refine ⟨6908923284697497560821229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4605948856464998373880819 6908923284697497560821229)
                    ·
                      refine ⟨2590846231761561585307961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908923284697497560821229 2590846231761561585307961)
                      ·
                        rfl

theorem cell23_5045655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_5045655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045655 prefixEnd_5045655 := by exact prefixLift 5045655
  have htrace : WordTrace (prefixWord ++ tailWord_5045655) baseStart_5045655 baseEnd_5045655 := by
    simpa [prefixWord, tailWord_5045655, baseEnd_5045655] using wordTrace_append hprefix tailTrace_5045655
  have hstable : (prefixWord ++ tailWord_5045655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045655).length < 2 ^ (prefixWord ++ tailWord_5045655).sum := by decide
  have hdescent : baseEnd_5045655 < baseStart_5045655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045656 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5045656 : Nat := 118140960795 + 5045656 * 2 ^ 59
def prefixEnd_5045656 : Nat := 4983230072969 + 3 ^ 40 * 5045656 * 2
def baseEnd_5045656 : Nat := 2590846745242216081395457

theorem tailTrace_5045656 : CollatzResearch.WordTrace tailWord_5045656 prefixEnd_5045656 2590846745242216081395457 := by
  unfold tailWord_5045656
  simp only [CollatzResearch.WordTrace]
  refine ⟨92015096504228758142062411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122686795338971677522749881 92015096504228758142062411)
  ·
    refine ⟨138022644756343137213093617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92015096504228758142062411 138022644756343137213093617)
    ·
      refine ⟨103516983567257352909820213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138022644756343137213093617 103516983567257352909820213)
      ·
        refine ⟨9704717209430376835295645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103516983567257352909820213 9704717209430376835295645)
        ·
          refine ⟨3639268953536391313235867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9704717209430376835295645 3639268953536391313235867)
          ·
            refine ⟨5458903430304586969853801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639268953536391313235867 5458903430304586969853801)
            ·
              refine ⟨4094177572728440227390351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458903430304586969853801 4094177572728440227390351)
              ·
                refine ⟨6141266359092660341085527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094177572728440227390351 6141266359092660341085527)
                ·
                  refine ⟨9211899538638990511628291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141266359092660341085527 9211899538638990511628291)
                  ·
                    refine ⟨13817849307958485767442437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9211899538638990511628291 13817849307958485767442437)
                    ·
                      refine ⟨2590846745242216081395457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13817849307958485767442437 2590846745242216081395457)
                      ·
                        rfl

theorem cell23_5045656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5045656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045656 prefixEnd_5045656 := by exact prefixLift 5045656
  have htrace : WordTrace (prefixWord ++ tailWord_5045656) baseStart_5045656 baseEnd_5045656 := by
    simpa [prefixWord, tailWord_5045656, baseEnd_5045656] using wordTrace_append hprefix tailTrace_5045656
  have hstable : (prefixWord ++ tailWord_5045656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045656).length < 2 ^ (prefixWord ++ tailWord_5045656).sum := by decide
  have hdescent : baseEnd_5045656 < baseStart_5045656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045688 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_5045688 : Nat := 118140960795 + 5045688 * 2 ^ 59
def prefixEnd_5045688 : Nat := 4983230072969 + 3 ^ 40 * 5045688 * 2
def baseEnd_5045688 : Nat := 863621058874386652065103

theorem tailTrace_5045688 : CollatzResearch.WordTrace tailWord_5045688 prefixEnd_5045688 863621058874386652065103 := by
  unfold tailWord_5045688
  simp only [CollatzResearch.WordTrace]
  refine ⟨92015680072170792874644859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122687573429561057166193145 92015680072170792874644859)
  ·
    refine ⟨138023520108256189311967289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92015680072170792874644859 138023520108256189311967289)
    ·
      refine ⟨103517640081192141983975467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138023520108256189311967289 103517640081192141983975467)
      ·
        refine ⟨155276460121788212975963201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103517640081192141983975467 155276460121788212975963201)
        ·
          refine ⟨116457345091341159731972401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155276460121788212975963201 116457345091341159731972401)
          ·
            refine ⟨87343008818505869798979301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116457345091341159731972401 87343008818505869798979301)
            ·
              refine ⟨16376814153469850587308619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87343008818505869798979301 16376814153469850587308619)
              ·
                refine ⟨24565221230204775880962929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16376814153469850587308619 24565221230204775880962929)
                ·
                  refine ⟨18423915922653581910722197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24565221230204775880962929 18423915922653581910722197)
                  ·
                    refine ⟨863621058874386652065103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18423915922653581910722197 863621058874386652065103)
                    ·
                      rfl

theorem cell23_5045688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_5045688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045688 prefixEnd_5045688 := by exact prefixLift 5045688
  have htrace : WordTrace (prefixWord ++ tailWord_5045688) baseStart_5045688 baseEnd_5045688 := by
    simpa [prefixWord, tailWord_5045688, baseEnd_5045688] using wordTrace_append hprefix tailTrace_5045688
  have hstable : (prefixWord ++ tailWord_5045688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045688).length < 2 ^ (prefixWord ++ tailWord_5045688).sum := by decide
  have hdescent : baseEnd_5045688 < baseStart_5045688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045689 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5045689 : Nat := 118140960795 + 5045689 * 2 ^ 59
def prefixEnd_5045689 : Nat := 4983230072969 + 3 ^ 40 * 5045689 * 2
def baseEnd_5045689 : Nat := 2590863690103814452282805

theorem tailTrace_5045689 : CollatzResearch.WordTrace tailWord_5045689 prefixEnd_5045689 2590863690103814452282805 := by
  unfold tailWord_5045689
  simp only [CollatzResearch.WordTrace]
  refine ⟨184031396617337962920076121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122687597744891975280050747 184031396617337962920076121)
  ·
    refine ⟨138023547463003472190057091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184031396617337962920076121 138023547463003472190057091)
    ·
      refine ⟨207035321194505208285085637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138023547463003472190057091 207035321194505208285085637)
      ·
        refine ⟨38819122723969726553453557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207035321194505208285085637 38819122723969726553453557)
        ·
          refine ⟨3639292755372161864386271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38819122723969726553453557 3639292755372161864386271)
          ·
            refine ⟨5458939133058242796579407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639292755372161864386271 5458939133058242796579407)
            ·
              refine ⟨8188408699587364194869111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458939133058242796579407 8188408699587364194869111)
              ·
                refine ⟨12282613049381046292303667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188408699587364194869111 12282613049381046292303667)
                ·
                  refine ⟨18423919574071569438455501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12282613049381046292303667 18423919574071569438455501)
                  ·
                    refine ⟨6908969840276838539420813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18423919574071569438455501 6908969840276838539420813)
                    ·
                      refine ⟨2590863690103814452282805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6908969840276838539420813 2590863690103814452282805)
                      ·
                        rfl

theorem cell23_5045689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5045689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045689 prefixEnd_5045689 := by exact prefixLift 5045689
  have htrace : WordTrace (prefixWord ++ tailWord_5045689) baseStart_5045689 baseEnd_5045689 := by
    simpa [prefixWord, tailWord_5045689, baseEnd_5045689] using wordTrace_append hprefix tailTrace_5045689
  have hstable : (prefixWord ++ tailWord_5045689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045689).length < 2 ^ (prefixWord ++ tailWord_5045689).sum := by decide
  have hdescent : baseEnd_5045689 < baseStart_5045689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045735 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 7]
def baseStart_5045735 : Nat := 118140960795 + 5045735 * 2 ^ 59
def prefixEnd_5045735 : Nat := 4983230072969 + 3 ^ 40 * 5045735 * 2
def baseEnd_5045735 : Nat := 287876367801546808034177

theorem tailTrace_5045735 : CollatzResearch.WordTrace tailWord_5045735 prefixEnd_5045735 287876367801546808034177 := by
  unfold tailWord_5045735
  simp only [CollatzResearch.WordTrace]
  refine ⟨184033074375171312776250659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122688716250114208517500439 184033074375171312776250659)
  ·
    refine ⟨276049611562756969164375989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184033074375171312776250659 276049611562756969164375989)
    ·
      refine ⟨25879651084008465859160249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276049611562756969164375989 25879651084008465859160249)
      ·
        refine ⟨19409738313006349394370187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25879651084008465859160249 19409738313006349394370187)
        ·
          refine ⟨29114607469509524091555281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19409738313006349394370187 29114607469509524091555281)
          ·
            refine ⟨21835955602132143068666461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29114607469509524091555281 21835955602132143068666461)
            ·
              refine ⟨8188483350799553650749923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21835955602132143068666461 8188483350799553650749923)
              ·
                refine ⟨12282725026199330476124885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188483350799553650749923 12282725026199330476124885)
                ·
                  refine ⟨287876367801546808034177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12282725026199330476124885 287876367801546808034177)
                  ·
                    rfl

theorem cell23_5045735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 7].length) (baseStart_5045735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045735 prefixEnd_5045735 := by exact prefixLift 5045735
  have htrace : WordTrace (prefixWord ++ tailWord_5045735) baseStart_5045735 baseEnd_5045735 := by
    simpa [prefixWord, tailWord_5045735, baseEnd_5045735] using wordTrace_append hprefix tailTrace_5045735
  have hstable : (prefixWord ++ tailWord_5045735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045735).length < 2 ^ (prefixWord ++ tailWord_5045735).sum := by decide
  have hdescent : baseEnd_5045735 < baseStart_5045735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045746 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5045746 : Nat := 118140960795 + 5045746 * 2 ^ 59
def prefixEnd_5045746 : Nat := 4983230072969 + 3 ^ 40 * 5045746 * 2
def baseEnd_5045746 : Nat := 2590892958501120729270043

theorem tailTrace_5045746 : CollatzResearch.WordTrace tailWord_5045746 prefixEnd_5045746 2590892958501120729270043 := by
  unfold tailWord_5045746
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008368894532865413725273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122688983718754307769934061 46008368894532865413725273)
  ·
    refine ⟨34506276670899649060293955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46008368894532865413725273 34506276670899649060293955)
    ·
      refine ⟨51759415006349473590440933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34506276670899649060293955 51759415006349473590440933)
      ·
        refine ⟨9704890313690526298207675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51759415006349473590440933 9704890313690526298207675)
        ·
          refine ⟨14557335470535789447311513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704890313690526298207675 14557335470535789447311513)
          ·
            refine ⟨10918001602901842085483635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14557335470535789447311513 10918001602901842085483635)
            ·
              refine ⟨16377002404352763128225453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10918001602901842085483635 16377002404352763128225453)
              ·
                refine ⟨6141375901632286173084545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16377002404352763128225453 6141375901632286173084545)
                ·
                  refine ⟨4606031926224214629813409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141375901632286173084545 4606031926224214629813409)
                  ·
                    refine ⟨3454523944668160972360057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606031926224214629813409 3454523944668160972360057)
                    ·
                      refine ⟨2590892958501120729270043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454523944668160972360057 2590892958501120729270043)
                      ·
                        rfl

theorem cell23_5045746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5045746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045746 prefixEnd_5045746 := by exact prefixLift 5045746
  have htrace : WordTrace (prefixWord ++ tailWord_5045746) baseStart_5045746 baseEnd_5045746 := by
    simpa [prefixWord, tailWord_5045746, baseEnd_5045746] using wordTrace_append hprefix tailTrace_5045746
  have hstable : (prefixWord ++ tailWord_5045746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045746).length < 2 ^ (prefixWord ++ tailWord_5045746).sum := by decide
  have hdescent : baseEnd_5045746 < baseStart_5045746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045755 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 5, 2]
def baseStart_5045755 : Nat := 118140960795 + 5045755 * 2 ^ 59
def prefixEnd_5045755 : Nat := 4983230072969 + 3 ^ 40 * 5045755 * 2
def baseEnd_5045755 : Nat := 2590897579827011194057501

theorem tailTrace_5045755 : CollatzResearch.WordTrace tailWord_5045755 prefixEnd_5045755 2590897579827011194057501 := by
  unfold tailWord_5045755
  simp only [CollatzResearch.WordTrace]
  refine ⟨184033803835098856191978719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122689202556732570794652479 184033803835098856191978719)
  ·
    refine ⟨276050705752648284287968079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184033803835098856191978719 276050705752648284287968079)
    ·
      refine ⟨414076058628972426431952119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276050705752648284287968079 414076058628972426431952119)
      ·
        refine ⟨621114087943458639647928179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414076058628972426431952119 621114087943458639647928179)
        ·
          refine ⟨931671131915187959471892269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621114087943458639647928179 931671131915187959471892269)
          ·
            refine ⟨349376674468195484801959601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 931671131915187959471892269 349376674468195484801959601)
            ·
              refine ⟨262032505851146613601469701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349376674468195484801959601 262032505851146613601469701)
              ·
                refine ⟨49131094847089990050275569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262032505851146613601469701 49131094847089990050275569)
                ·
                  refine ⟨36848321135317492537706677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49131094847089990050275569 36848321135317492537706677)
                  ·
                    refine ⟨3454530106436014925410001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36848321135317492537706677 3454530106436014925410001)
                    ·
                      refine ⟨2590897579827011194057501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454530106436014925410001 2590897579827011194057501)
                      ·
                        rfl

theorem cell23_5045755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5, 2].length) (baseStart_5045755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045755 prefixEnd_5045755 := by exact prefixLift 5045755
  have htrace : WordTrace (prefixWord ++ tailWord_5045755) baseStart_5045755 baseEnd_5045755 := by
    simpa [prefixWord, tailWord_5045755, baseEnd_5045755] using wordTrace_append hprefix tailTrace_5045755
  have hstable : (prefixWord ++ tailWord_5045755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045755).length < 2 ^ (prefixWord ++ tailWord_5045755).sum := by decide
  have hdescent : baseEnd_5045755 < baseStart_5045755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045808 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 10]
def baseStart_5045808 : Nat := 118140960795 + 5045808 * 2 ^ 59
def prefixEnd_5045808 : Nat := 4983230072969 + 3 ^ 40 * 5045808 * 2
def baseEnd_5045808 : Nat := 287880532700188831854973

theorem tailTrace_5045808 : CollatzResearch.WordTrace tailWord_5045808 prefixEnd_5045808 287880532700188831854973 := by
  unfold tailWord_5045808
  simp only [CollatzResearch.WordTrace]
  refine ⟨92017868451953423121829039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122690491269271230829105385 92017868451953423121829039)
  ·
    refine ⟨138026802677930134682743559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92017868451953423121829039 138026802677930134682743559)
    ·
      refine ⟨207040204016895202024115339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138026802677930134682743559 207040204016895202024115339)
      ·
        refine ⟨310560306025342803036173009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207040204016895202024115339 310560306025342803036173009)
        ·
          refine ⟨232920229519007102277129757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310560306025342803036173009 232920229519007102277129757)
          ·
            refine ⟨87345086069627663353923659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232920229519007102277129757 87345086069627663353923659)
            ·
              refine ⟨131017629104441495030885489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87345086069627663353923659 131017629104441495030885489)
              ·
                refine ⟨98263221828331121273164117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131017629104441495030885489 98263221828331121273164117)
                ·
                  refine ⟨287880532700188831854973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98263221828331121273164117 287880532700188831854973)
                  ·
                    rfl

theorem cell23_5045808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_5045808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045808 prefixEnd_5045808 := by exact prefixLift 5045808
  have htrace : WordTrace (prefixWord ++ tailWord_5045808) baseStart_5045808 baseEnd_5045808 := by
    simpa [prefixWord, tailWord_5045808, baseEnd_5045808] using wordTrace_append hprefix tailTrace_5045808
  have hstable : (prefixWord ++ tailWord_5045808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045808).length < 2 ^ (prefixWord ++ tailWord_5045808).sum := by decide
  have hdescent : baseEnd_5045808 < baseStart_5045808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045825 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 8]
def baseStart_5045825 : Nat := 118140960795 + 5045825 * 2 ^ 59
def prefixEnd_5045825 : Nat := 4983230072969 + 3 ^ 40 * 5045825 * 2
def baseEnd_5045825 : Nat := 287881502608091768909131

theorem tailTrace_5045825 : CollatzResearch.WordTrace tailWord_5045825 prefixEnd_5045825 287881502608091768909131 := by
  unfold tailWord_5045825
  simp only [CollatzResearch.WordTrace]
  refine ⟨184036356944845258147026929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122690904629896838764684619 184036356944845258147026929)
  ·
    refine ⟨138027267708633943610270197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184036356944845258147026929 138027267708633943610270197)
    ·
      refine ⟨12940056347684432213462831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138027267708633943610270197 12940056347684432213462831)
      ·
        refine ⟨19410084521526648320194247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12940056347684432213462831 19410084521526648320194247)
        ·
          refine ⟨29115126782289972480291371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19410084521526648320194247 29115126782289972480291371)
          ·
            refine ⟨43672690173434958720437057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29115126782289972480291371 43672690173434958720437057)
            ·
              refine ⟨32754517630076219040327793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43672690173434958720437057 32754517630076219040327793)
              ·
                refine ⟨24565888222557164280245845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32754517630076219040327793 24565888222557164280245845)
                ·
                  refine ⟨287881502608091768909131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24565888222557164280245845 287881502608091768909131)
                  ·
                    rfl

theorem cell23_5045825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_5045825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045825 prefixEnd_5045825 := by exact prefixLift 5045825
  have htrace : WordTrace (prefixWord ++ tailWord_5045825) baseStart_5045825 baseEnd_5045825 := by
    simpa [prefixWord, tailWord_5045825, baseEnd_5045825] using wordTrace_append hprefix tailTrace_5045825
  have hstable : (prefixWord ++ tailWord_5045825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045825).length < 2 ^ (prefixWord ++ tailWord_5045825).sum := by decide
  have hdescent : baseEnd_5045825 < baseStart_5045825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045829 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_5045829 : Nat := 118140960795 + 5045829 * 2 ^ 59
def prefixEnd_5045829 : Nat := 4983230072969 + 3 ^ 40 * 5045829 * 2
def baseEnd_5045829 : Nat := 863645192465147968177387

theorem tailTrace_5045829 : CollatzResearch.WordTrace tailWord_5045829 prefixEnd_5045829 863645192465147968177387 := by
  unfold tailWord_5045829
  simp only [CollatzResearch.WordTrace]
  refine ⟨184036502836830766830172541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122691001891220511220115027 184036502836830766830172541)
  ·
    refine ⟨69013688563811537561314703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184036502836830766830172541 69013688563811537561314703)
    ·
      refine ⟨103520532845717306341972055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69013688563811537561314703 103520532845717306341972055)
      ·
        refine ⟨155280799268575959512958083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103520532845717306341972055 155280799268575959512958083)
        ·
          refine ⟨232921198902863939269437125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155280799268575959512958083 232921198902863939269437125)
          ·
            refine ⟨43672724794286988613019461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232921198902863939269437125 43672724794286988613019461)
            ·
              refine ⟨8188635898928810364941149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43672724794286988613019461 8188635898928810364941149)
              ·
                refine ⟨3070738462098303886852931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8188635898928810364941149 3070738462098303886852931)
                ·
                  refine ⟨4606107693147455830279397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070738462098303886852931 4606107693147455830279397)
                  ·
                    refine ⟨863645192465147968177387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606107693147455830279397 863645192465147968177387)
                    ·
                      rfl

theorem cell23_5045829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_5045829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045829 prefixEnd_5045829 := by exact prefixLift 5045829
  have htrace : WordTrace (prefixWord ++ tailWord_5045829) baseStart_5045829 baseEnd_5045829 := by
    simpa [prefixWord, tailWord_5045829, baseEnd_5045829] using wordTrace_append hprefix tailTrace_5045829
  have hstable : (prefixWord ++ tailWord_5045829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045829).length < 2 ^ (prefixWord ++ tailWord_5045829).sum := by decide
  have hdescent : baseEnd_5045829 < baseStart_5045829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045842 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_5045842 : Nat := 118140960795 + 5045842 * 2 ^ 59
def prefixEnd_5045842 : Nat := 4983230072969 + 3 ^ 40 * 5045842 * 2
def baseEnd_5045842 : Nat := 287882472515994705963289

theorem tailTrace_5045842 : CollatzResearch.WordTrace tailWord_5045842 prefixEnd_5045842 287882472515994705963289 := by
  unfold tailWord_5045842
  simp only [CollatzResearch.WordTrace]
  refine ⟨46009244246445917512598945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122691317990522446700263853 46009244246445917512598945)
  ·
    refine ⟨34506933184834438134449209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46009244246445917512598945 34506933184834438134449209)
    ·
      refine ⟨25880199888625828600836907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34506933184834438134449209 25880199888625828600836907)
      ·
        refine ⟨38820299832938742901255361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25880199888625828600836907 38820299832938742901255361)
        ·
          refine ⟨29115224874704057175941521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38820299832938742901255361 29115224874704057175941521)
          ·
            refine ⟨21836418656028042881956141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29115224874704057175941521 21836418656028042881956141)
            ·
              refine ⟨8188656996010516080733553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21836418656028042881956141 8188656996010516080733553)
              ·
                refine ⟨6141492747007887060550165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8188656996010516080733553 6141492747007887060550165)
                ·
                  refine ⟨287882472515994705963289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6141492747007887060550165 287882472515994705963289)
                  ·
                    rfl

theorem cell23_5045842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_5045842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045842 prefixEnd_5045842 := by exact prefixLift 5045842
  have htrace : WordTrace (prefixWord ++ tailWord_5045842) baseStart_5045842 baseEnd_5045842 := by
    simpa [prefixWord, tailWord_5045842, baseEnd_5045842] using wordTrace_append hprefix tailTrace_5045842
  have hstable : (prefixWord ++ tailWord_5045842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045842).length < 2 ^ (prefixWord ++ tailWord_5045842).sum := by decide
  have hdescent : baseEnd_5045842 < baseStart_5045842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045872 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_5045872 : Nat := 118140960795 + 5045872 * 2 ^ 59
def prefixEnd_5045872 : Nat := 4983230072969 + 3 ^ 40 * 5045872 * 2
def baseEnd_5045872 : Nat := 863652552354529078764821

theorem tailTrace_5045872 : CollatzResearch.WordTrace tailWord_5045872 prefixEnd_5045872 863652552354529078764821 := by
  unfold tailWord_5045872
  simp only [CollatzResearch.WordTrace]
  refine ⟨92019035587837492586993935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122692047450449990115991913 92019035587837492586993935)
  ·
    refine ⟨138028553381756238880490903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92019035587837492586993935 138028553381756238880490903)
    ·
      refine ⟨207042830072634358320736355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138028553381756238880490903 207042830072634358320736355)
      ·
        refine ⟨310564245108951537481104533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207042830072634358320736355 310564245108951537481104533)
        ·
          refine ⟨14557698989482103319426775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 310564245108951537481104533 14557698989482103319426775)
          ·
            refine ⟨21836548484223154979140163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14557698989482103319426775 21836548484223154979140163)
            ·
              refine ⟨32754822726334732468710245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21836548484223154979140163 32754822726334732468710245)
              ·
                refine ⟨6141529261187762337883171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32754822726334732468710245 6141529261187762337883171)
                ·
                  refine ⟨9212293891781643506824757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141529261187762337883171 9212293891781643506824757)
                  ·
                    refine ⟨863652552354529078764821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9212293891781643506824757 863652552354529078764821)
                    ·
                      rfl

theorem cell23_5045872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_5045872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045872 prefixEnd_5045872 := by exact prefixLift 5045872
  have htrace : WordTrace (prefixWord ++ tailWord_5045872) baseStart_5045872 baseEnd_5045872 := by
    simpa [prefixWord, tailWord_5045872, baseEnd_5045872] using wordTrace_append hprefix tailTrace_5045872
  have hstable : (prefixWord ++ tailWord_5045872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045872).length < 2 ^ (prefixWord ++ tailWord_5045872).sum := by decide
  have hdescent : baseEnd_5045872 < baseStart_5045872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045875 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4]
def baseStart_5045875 : Nat := 118140960795 + 5045875 * 2 ^ 59
def prefixEnd_5045875 : Nat := 4983230072969 + 3 ^ 40 * 5045875 * 2
def baseEnd_5045875 : Nat := 2590959197505550724556949

theorem tailTrace_5045875 : CollatzResearch.WordTrace tailWord_5045875 prefixEnd_5045875 2590959197505550724556949 := by
  unfold tailWord_5045875
  simp only [CollatzResearch.WordTrace]
  refine ⟨184038180594664116686347079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122692120396442744457564719 184038180594664116686347079)
  ·
    refine ⟨276057270891996175029520619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184038180594664116686347079 276057270891996175029520619)
    ·
      refine ⟨414085906337994262544280929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276057270891996175029520619 414085906337994262544280929)
      ·
        refine ⟨310564429753495696908210697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414085906337994262544280929 310564429753495696908210697)
        ·
          refine ⟨232923322315121772681158023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310564429753495696908210697 232923322315121772681158023)
          ·
            refine ⟨349384983472682659021737035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232923322315121772681158023 349384983472682659021737035)
            ·
              refine ⟨524077475209023988532605553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349384983472682659021737035 524077475209023988532605553)
              ·
                refine ⟨393058106406767991399454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524077475209023988532605553 393058106406767991399454165)
                ·
                  refine ⟨9212299368908624798424707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 393058106406767991399454165 9212299368908624798424707)
                  ·
                    refine ⟨13818449053362937197637061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9212299368908624798424707 13818449053362937197637061)
                    ·
                      refine ⟨2590959197505550724556949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13818449053362937197637061 2590959197505550724556949)
                      ·
                        rfl

theorem cell23_5045875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_5045875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045875 prefixEnd_5045875 := by exact prefixLift 5045875
  have htrace : WordTrace (prefixWord ++ tailWord_5045875) baseStart_5045875 baseEnd_5045875 := by
    simpa [prefixWord, tailWord_5045875, baseEnd_5045875] using wordTrace_append hprefix tailTrace_5045875
  have hstable : (prefixWord ++ tailWord_5045875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045875).length < 2 ^ (prefixWord ++ tailWord_5045875).sum := by decide
  have hdescent : baseEnd_5045875 < baseStart_5045875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045905 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_5045905 : Nat := 118140960795 + 5045905 * 2 ^ 59
def prefixEnd_5045905 : Nat := 4983230072969 + 3 ^ 40 * 5045905 * 2
def baseEnd_5045905 : Nat := 2590974601925185607181811

theorem tailTrace_5045905 : CollatzResearch.WordTrace tailWord_5045905 prefixEnd_5045905 2590974601925185607181811 := by
  unfold tailWord_5045905
  simp only [CollatzResearch.WordTrace]
  refine ⟨184039274784555431809939169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122692849856370287873292779 184039274784555431809939169)
  ·
    refine ⟨138029456088416573857454377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184039274784555431809939169 138029456088416573857454377)
    ·
      refine ⟨103522092066312430393090783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138029456088416573857454377 103522092066312430393090783)
      ·
        refine ⟨155283138099468645589636175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103522092066312430393090783 155283138099468645589636175)
        ·
          refine ⟨232924707149202968384454263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155283138099468645589636175 232924707149202968384454263)
          ·
            refine ⟨349387060723804452576681395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232924707149202968384454263 349387060723804452576681395)
            ·
              refine ⟨524080591085706678865022093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349387060723804452576681395 524080591085706678865022093)
              ·
                refine ⟨196530221657140004574383285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524080591085706678865022093 196530221657140004574383285)
                ·
                  refine ⟨18424708280356875428848433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196530221657140004574383285 18424708280356875428848433)
                  ·
                    refine ⟨13818531210267656571636325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18424708280356875428848433 13818531210267656571636325)
                    ·
                      refine ⟨2590974601925185607181811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13818531210267656571636325 2590974601925185607181811)
                      ·
                        rfl

theorem cell23_5045905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_5045905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045905 prefixEnd_5045905 := by exact prefixLift 5045905
  have htrace : WordTrace (prefixWord ++ tailWord_5045905) baseStart_5045905 baseEnd_5045905 := by
    simpa [prefixWord, tailWord_5045905, baseEnd_5045905] using wordTrace_append hprefix tailTrace_5045905
  have hstable : (prefixWord ++ tailWord_5045905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045905).length < 2 ^ (prefixWord ++ tailWord_5045905).sum := by decide
  have hdescent : baseEnd_5045905 < baseStart_5045905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045912 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5045912 : Nat := 118140960795 + 5045912 * 2 ^ 59
def prefixEnd_5045912 : Nat := 4983230072969 + 3 ^ 40 * 5045912 * 2
def baseEnd_5045912 : Nat := 2590978196289767079794279

theorem tailTrace_5045912 : CollatzResearch.WordTrace tailWord_5045912 prefixEnd_5045912 2590978196289767079794279 := by
  unfold tailWord_5045912
  simp only [CollatzResearch.WordTrace]
  refine ⟨92019765047765036002721995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122693020063686714670295993 92019765047765036002721995)
  ·
    refine ⟨138029647571647554004082993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92019765047765036002721995 138029647571647554004082993)
    ·
      refine ⟨103522235678735665503062245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138029647571647554004082993 103522235678735665503062245)
      ·
        refine ⟨19410419189762937281824171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103522235678735665503062245 19410419189762937281824171)
        ·
          refine ⟨29115628784644405922736257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19410419189762937281824171 29115628784644405922736257)
          ·
            refine ⟨21836721588483304442052193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29115628784644405922736257 21836721588483304442052193)
            ·
              refine ⟨16377541191362478331539145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21836721588483304442052193 16377541191362478331539145)
              ·
                refine ⟨12283155893521858748654359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16377541191362478331539145 12283155893521858748654359)
                ·
                  refine ⟨18424733840282788122981539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12283155893521858748654359 18424733840282788122981539)
                  ·
                    refine ⟨27637100760424182184472309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18424733840282788122981539 27637100760424182184472309)
                    ·
                      refine ⟨2590978196289767079794279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27637100760424182184472309 2590978196289767079794279)
                      ·
                        rfl

theorem cell23_5045912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5045912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045912 prefixEnd_5045912 := by exact prefixLift 5045912
  have htrace : WordTrace (prefixWord ++ tailWord_5045912) baseStart_5045912 baseEnd_5045912 := by
    simpa [prefixWord, tailWord_5045912, baseEnd_5045912] using wordTrace_append hprefix tailTrace_5045912
  have hstable : (prefixWord ++ tailWord_5045912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045912).length < 2 ^ (prefixWord ++ tailWord_5045912).sum := by decide
  have hdescent : baseEnd_5045912 < baseStart_5045912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045946 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_5045946 : Nat := 118140960795 + 5045946 * 2 ^ 59
def prefixEnd_5045946 : Nat := 4983230072969 + 3 ^ 40 * 5045946 * 2
def baseEnd_5045946 : Nat := 2590995654632019946769123

theorem tailTrace_5045946 : CollatzResearch.WordTrace tailWord_5045946 prefixEnd_5045946 2590995654632019946769123 := by
  unfold tailWord_5045946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46010192544351723953045423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122693846784937930541454461 46010192544351723953045423)
  ·
    refine ⟨69015288816527585929568135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46010192544351723953045423 69015288816527585929568135)
    ·
      refine ⟨103522933224791378894352203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69015288816527585929568135 103522933224791378894352203)
      ·
        refine ⟨155284399837187068341528305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103522933224791378894352203 155284399837187068341528305)
        ·
          refine ⟨116463299877890301256146229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155284399837187068341528305 116463299877890301256146229)
          ·
            refine ⟨10918434363552215742763709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116463299877890301256146229 10918434363552215742763709)
            ·
              refine ⟨4094412886332080903536391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10918434363552215742763709 4094412886332080903536391)
              ·
                refine ⟨6141619329498121355304587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094412886332080903536391 6141619329498121355304587)
                ·
                  refine ⟨9212428994247182032956881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141619329498121355304587 9212428994247182032956881)
                  ·
                    refine ⟨6909321745685386524717661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9212428994247182032956881 6909321745685386524717661)
                    ·
                      refine ⟨2590995654632019946769123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6909321745685386524717661 2590995654632019946769123)
                      ·
                        rfl

theorem cell23_5045946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_5045946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045946 prefixEnd_5045946 := by exact prefixLift 5045946
  have htrace : WordTrace (prefixWord ++ tailWord_5045946) baseStart_5045946 baseEnd_5045946 := by
    simpa [prefixWord, tailWord_5045946, baseEnd_5045946] using wordTrace_append hprefix tailTrace_5045946
  have hstable : (prefixWord ++ tailWord_5045946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045946).length < 2 ^ (prefixWord ++ tailWord_5045946).sum := by decide
  have hdescent : baseEnd_5045946 < baseStart_5045946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045969 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_5045969 : Nat := 118140960795 + 5045969 * 2 ^ 59
def prefixEnd_5045969 : Nat := 4983230072969 + 3 ^ 40 * 5045969 * 2
def baseEnd_5045969 : Nat := 2591007464687073356781517

theorem tailTrace_5045969 : CollatzResearch.WordTrace tailWord_5045969 prefixEnd_5045969 2591007464687073356781517 := by
  unfold tailWord_5045969
  simp only [CollatzResearch.WordTrace]
  refine ⟨184041609056323570740268961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122694406037549047160179307 184041609056323570740268961)
  ·
    refine ⟨138031206792242678055201721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184041609056323570740268961 138031206792242678055201721)
    ·
      refine ⟨103523405094182008541401291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138031206792242678055201721 103523405094182008541401291)
      ·
        refine ⟨155285107641273012812101937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103523405094182008541401291 155285107641273012812101937)
        ·
          refine ⟨116463830730954759609076453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155285107641273012812101937 116463830730954759609076453)
          ·
            refine ⟨21836968262054017426701835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116463830730954759609076453 21836968262054017426701835)
            ·
              refine ⟨32755452393081026140052753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21836968262054017426701835 32755452393081026140052753)
              ·
                refine ⟨24566589294810769605039565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32755452393081026140052753 24566589294810769605039565)
                ·
                  refine ⟨9212470985554038601889837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24566589294810769605039565 9212470985554038601889837)
                  ·
                    refine ⟨3454676619582764475708689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9212470985554038601889837 3454676619582764475708689)
                    ·
                      refine ⟨2591007464687073356781517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454676619582764475708689 2591007464687073356781517)
                      ·
                        rfl

theorem cell23_5045969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_5045969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045969 prefixEnd_5045969 := by exact prefixLift 5045969
  have htrace : WordTrace (prefixWord ++ tailWord_5045969) baseStart_5045969 baseEnd_5045969 := by
    simpa [prefixWord, tailWord_5045969, baseEnd_5045969] using wordTrace_append hprefix tailTrace_5045969
  have hstable : (prefixWord ++ tailWord_5045969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045969).length < 2 ^ (prefixWord ++ tailWord_5045969).sum := by decide
  have hdescent : baseEnd_5045969 < baseStart_5045969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5045999 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 1, 4, 2]
def baseStart_5045999 : Nat := 118140960795 + 5045999 * 2 ^ 59
def prefixEnd_5045999 : Nat := 4983230072969 + 3 ^ 40 * 5045999 * 2
def baseEnd_5045999 : Nat := 2591022869106708239406379

theorem tailTrace_5045999 : CollatzResearch.WordTrace tailWord_5045999 prefixEnd_5045999 2591022869106708239406379 := by
  unfold tailWord_5045999
  simp only [CollatzResearch.WordTrace]
  refine ⟨184042703246214885863861051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122695135497476590575907367 184042703246214885863861051)
  ·
    refine ⟨276064054869322328795791577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184042703246214885863861051 276064054869322328795791577)
    ·
      refine ⟨207048041151991746596843683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276064054869322328795791577 207048041151991746596843683)
      ·
        refine ⟨310572061727987619895265525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207048041151991746596843683 310572061727987619895265525)
        ·
          refine ⟨29116130786998839365181143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 310572061727987619895265525 29116130786998839365181143)
          ·
            refine ⟨43674196180498259047771715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29116130786998839365181143 43674196180498259047771715)
            ·
              refine ⟨65511294270747388571657573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43674196180498259047771715 65511294270747388571657573)
              ·
                refine ⟨12283367675765135357185795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65511294270747388571657573 12283367675765135357185795)
                ·
                  refine ⟨18425051513647703035778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12283367675765135357185795 18425051513647703035778693)
                  ·
                    refine ⟨3454697158808944319208505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18425051513647703035778693 3454697158808944319208505)
                    ·
                      refine ⟨2591022869106708239406379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454697158808944319208505 2591022869106708239406379)
                      ·
                        rfl

theorem cell23_5045999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4, 2].length) (baseStart_5045999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5045999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5045999 prefixEnd_5045999 := by exact prefixLift 5045999
  have htrace : WordTrace (prefixWord ++ tailWord_5045999) baseStart_5045999 baseEnd_5045999 := by
    simpa [prefixWord, tailWord_5045999, baseEnd_5045999] using wordTrace_append hprefix tailTrace_5045999
  have hstable : (prefixWord ++ tailWord_5045999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5045999).length < 2 ^ (prefixWord ++ tailWord_5045999).sum := by decide
  have hdescent : baseEnd_5045999 < baseStart_5045999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5045999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046002 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5046002 : Nat := 118140960795 + 5046002 * 2 ^ 59
def prefixEnd_5046002 : Nat := 4983230072969 + 3 ^ 40 * 5046002 * 2
def baseEnd_5046002 : Nat := 2591024409548671727668865

theorem tailTrace_5046002 : CollatzResearch.WordTrace tailWord_5046002 prefixEnd_5046002 2591024409548671727668865 := by
  unfold tailWord_5046002
  simp only [CollatzResearch.WordTrace]
  refine ⟨46010703166301004344055065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122695208443469344917480173 46010703166301004344055065)
  ·
    refine ⟨34508027374725753258041299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46010703166301004344055065 34508027374725753258041299)
    ·
      refine ⟨51762041062088629887061949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34508027374725753258041299 51762041062088629887061949)
      ·
        refine ⟨19410765398283236207648231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51762041062088629887061949 19410765398283236207648231)
        ·
          refine ⟨29116148097424854311472347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19410765398283236207648231 29116148097424854311472347)
          ·
            refine ⟨43674222146137281467208521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29116148097424854311472347 43674222146137281467208521)
            ·
              refine ⟨32755666609602961100406391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43674222146137281467208521 32755666609602961100406391)
              ·
                refine ⟨49133499914404441650609587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32755666609602961100406391 49133499914404441650609587)
                ·
                  refine ⟨73700249871606662475914381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49133499914404441650609587 73700249871606662475914381)
                  ·
                    refine ⟨27637593701852498428467893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73700249871606662475914381 27637593701852498428467893)
                    ·
                      refine ⟨2591024409548671727668865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27637593701852498428467893 2591024409548671727668865)
                      ·
                        rfl

theorem cell23_5046002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5046002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046002 prefixEnd_5046002 := by exact prefixLift 5046002
  have htrace : WordTrace (prefixWord ++ tailWord_5046002) baseStart_5046002 baseEnd_5046002 := by
    simpa [prefixWord, tailWord_5046002, baseEnd_5046002] using wordTrace_append hprefix tailTrace_5046002
  have hstable : (prefixWord ++ tailWord_5046002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046002).length < 2 ^ (prefixWord ++ tailWord_5046002).sum := by decide
  have hdescent : baseEnd_5046002 < baseStart_5046002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046012 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_5046012 : Nat := 118140960795 + 5046012 * 2 ^ 59
def prefixEnd_5046012 : Nat := 4983230072969 + 3 ^ 40 * 5046012 * 2
def baseEnd_5046012 : Nat := 2591029544355216688543819

theorem tailTrace_5046012 : CollatzResearch.WordTrace tailWord_5046012 prefixEnd_5046012 2591029544355216688543819 := by
  unfold tailWord_5046012
  simp only [CollatzResearch.WordTrace]
  refine ⟨92021588697583894542042145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122695451596778526056056193 92021588697583894542042145)
  ·
    refine ⟨69016191523187920906531609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92021588697583894542042145 69016191523187920906531609)
    ·
      refine ⟨51762143642390940679898707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69016191523187920906531609 51762143642390940679898707)
      ·
        refine ⟨77643215463586411019848061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51762143642390940679898707 77643215463586411019848061)
        ·
          refine ⟨29116205798844904132443023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77643215463586411019848061 29116205798844904132443023)
          ·
            refine ⟨43674308698267356198664535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29116205798844904132443023 43674308698267356198664535)
            ·
              refine ⟨65511463047401034297996803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43674308698267356198664535 65511463047401034297996803)
              ·
                refine ⟨98267194571101551446995205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65511463047401034297996803 98267194571101551446995205)
                ·
                  refine ⟨18425098982081540896311601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98267194571101551446995205 18425098982081540896311601)
                  ·
                    refine ⟨13818824236561155672233701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18425098982081540896311601 13818824236561155672233701)
                    ·
                      refine ⟨2591029544355216688543819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13818824236561155672233701 2591029544355216688543819)
                      ·
                        rfl

theorem cell23_5046012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_5046012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046012 prefixEnd_5046012 := by exact prefixLift 5046012
  have htrace : WordTrace (prefixWord ++ tailWord_5046012) baseStart_5046012 baseEnd_5046012 := by
    simpa [prefixWord, tailWord_5046012, baseEnd_5046012] using wordTrace_append hprefix tailTrace_5046012
  have hstable : (prefixWord ++ tailWord_5046012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046012).length < 2 ^ (prefixWord ++ tailWord_5046012).sum := by decide
  have hdescent : baseEnd_5046012 < baseStart_5046012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046056 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 5]
def baseStart_5046056 : Nat := 118140960795 + 5046056 * 2 ^ 59
def prefixEnd_5046056 : Nat := 4983230072969 + 3 ^ 40 * 5046056 * 2
def baseEnd_5046056 : Nat := 287894681944890501821513

theorem tailTrace_5046056 : CollatzResearch.WordTrace tailWord_5046056 prefixEnd_5046056 287894681944890501821513 := by
  unfold tailWord_5046056
  simp only [CollatzResearch.WordTrace]
  refine ⟨92022391103504192299343011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122696521471338923065790681 92022391103504192299343011)
  ·
    refine ⟨138033586655256288449014517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92022391103504192299343011 138033586655256288449014517)
    ·
      refine ⟨12940648748930277042095111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138033586655256288449014517 12940648748930277042095111)
      ·
        refine ⟨19410973123395415563142667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12940648748930277042095111 19410973123395415563142667)
        ·
          refine ⟨29116459685093123344714001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19410973123395415563142667 29116459685093123344714001)
          ·
            refine ⟨21837344763819842508535501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29116459685093123344714001 21837344763819842508535501)
            ·
              refine ⟨8189004286432440940700813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21837344763819842508535501 8189004286432440940700813)
              ·
                refine ⟨3070876607412165352762805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8189004286432440940700813 3070876607412165352762805)
                ·
                  refine ⟨287894681944890501821513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3070876607412165352762805 287894681944890501821513)
                  ·
                    rfl

theorem cell23_5046056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 5].length) (baseStart_5046056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046056 prefixEnd_5046056 := by exact prefixLift 5046056
  have htrace : WordTrace (prefixWord ++ tailWord_5046056) baseStart_5046056 baseEnd_5046056 := by
    simpa [prefixWord, tailWord_5046056, baseEnd_5046056] using wordTrace_append hprefix tailTrace_5046056
  have hstable : (prefixWord ++ tailWord_5046056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046056).length < 2 ^ (prefixWord ++ tailWord_5046056).sum := by decide
  have hdescent : baseEnd_5046056 < baseStart_5046056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046073 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 7]
def baseStart_5046073 : Nat := 118140960795 + 5046073 * 2 ^ 59
def prefixEnd_5046073 : Nat := 4983230072969 + 3 ^ 40 * 5046073 * 2
def baseEnd_5046073 : Nat := 287895651852793438875671

theorem tailTrace_5046073 : CollatzResearch.WordTrace tailWord_5046073 prefixEnd_5046073 287895651852793438875671 := by
  unfold tailWord_5046073
  simp only [CollatzResearch.WordTrace]
  refine ⟨184045402247946796502054873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122696934831964531001369915 184045402247946796502054873)
  ·
    refine ⟨138034051685960097376541155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184045402247946796502054873 138034051685960097376541155)
    ·
      refine ⟨207051077528940146064811733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138034051685960097376541155 207051077528940146064811733)
      ·
        refine ⟨4852759629584534673394025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 207051077528940146064811733 4852759629584534673394025)
        ·
          refine ⟨3639569722188401005045519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4852759629584534673394025 3639569722188401005045519)
          ·
            refine ⟨5459354583282601507568279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639569722188401005045519 5459354583282601507568279)
            ·
              refine ⟨8189031874923902261352419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459354583282601507568279 8189031874923902261352419)
              ·
                refine ⟨12283547812385853392028629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8189031874923902261352419 12283547812385853392028629)
                ·
                  refine ⟨287895651852793438875671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12283547812385853392028629 287895651852793438875671)
                  ·
                    rfl

theorem cell23_5046073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 7].length) (baseStart_5046073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046073 prefixEnd_5046073 := by exact prefixLift 5046073
  have htrace : WordTrace (prefixWord ++ tailWord_5046073) baseStart_5046073 baseEnd_5046073 := by
    simpa [prefixWord, tailWord_5046073, baseEnd_5046073] using wordTrace_append hprefix tailTrace_5046073
  have hstable : (prefixWord ++ tailWord_5046073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046073).length < 2 ^ (prefixWord ++ tailWord_5046073).sum := by decide
  have hdescent : baseEnd_5046073 < baseStart_5046073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046079 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_5046079 : Nat := 118140960795 + 5046079 * 2 ^ 59
def prefixEnd_5046079 : Nat := 4983230072969 + 3 ^ 40 * 5046079 * 2
def baseEnd_5046079 : Nat := 2591063947559067926406011

theorem tailTrace_5046079 : CollatzResearch.WordTrace tailWord_5046079 prefixEnd_5046079 2591063947559067926406011 := by
  unfold tailWord_5046079
  simp only [CollatzResearch.WordTrace]
  refine ⟨184045621085925059526773291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122697080723950039684515527 184045621085925059526773291)
  ·
    refine ⟨276068431628887589290159937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184045621085925059526773291 276068431628887589290159937)
    ·
      refine ⟨207051323721665691967619953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276068431628887589290159937 207051323721665691967619953)
      ·
        refine ⟨155288492791249268975714965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207051323721665691967619953 155288492791249268975714965)
        ·
          refine ⟨7279148099589809483236639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155288492791249268975714965 7279148099589809483236639)
          ·
            refine ⟨10918722149384714224854959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279148099589809483236639 10918722149384714224854959)
            ·
              refine ⟨16378083224077071337282439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10918722149384714224854959 16378083224077071337282439)
              ·
                refine ⟨24567124836115607005923659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16378083224077071337282439 24567124836115607005923659)
                ·
                  refine ⟨36850687254173410508885489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24567124836115607005923659 36850687254173410508885489)
                  ·
                    refine ⟨27638015440630057881664117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36850687254173410508885489 27638015440630057881664117)
                    ·
                      refine ⟨2591063947559067926406011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27638015440630057881664117 2591063947559067926406011)
                      ·
                        rfl

theorem cell23_5046079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_5046079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046079 prefixEnd_5046079 := by exact prefixLift 5046079
  have htrace : WordTrace (prefixWord ++ tailWord_5046079) baseStart_5046079 baseEnd_5046079 := by
    simpa [prefixWord, tailWord_5046079, baseEnd_5046079] using wordTrace_append hprefix tailTrace_5046079
  have hstable : (prefixWord ++ tailWord_5046079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046079).length < 2 ^ (prefixWord ++ tailWord_5046079).sum := by decide
  have hdescent : baseEnd_5046079 < baseStart_5046079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046089 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 6, 2]
def baseStart_5046089 : Nat := 118140960795 + 5046089 * 2 ^ 59
def prefixEnd_5046089 : Nat := 4983230072969 + 3 ^ 40 * 5046089 * 2
def baseEnd_5046089 : Nat := 2591069082365612887280965

theorem tailTrace_5046089 : CollatzResearch.WordTrace tailWord_5046089 prefixEnd_5046089 2591069082365612887280965 := by
  unfold tailWord_5046089
  simp only [CollatzResearch.WordTrace]
  refine ⟨184045985815888831234637321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122697323877259220823091547 184045985815888831234637321)
  ·
    refine ⟨138034489361916623425977991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184045985815888831234637321 138034489361916623425977991)
    ·
      refine ⟨207051734042874935138966987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138034489361916623425977991 207051734042874935138966987)
      ·
        refine ⟨310577601064312402708450481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207051734042874935138966987 310577601064312402708450481)
        ·
          refine ⟨232933200798234302031337861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310577601064312402708450481 232933200798234302031337861)
          ·
            refine ⟨43674975149668931630875849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232933200798234302031337861 43674975149668931630875849)
            ·
              refine ⟨32756231362251698723156887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43674975149668931630875849 32756231362251698723156887)
              ·
                refine ⟨49134347043377548084735331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32756231362251698723156887 49134347043377548084735331)
                ·
                  refine ⟨73701520565066322127102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49134347043377548084735331 73701520565066322127102997)
                  ·
                    refine ⟨3454758776487483849707953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73701520565066322127102997 3454758776487483849707953)
                    ·
                      refine ⟨2591069082365612887280965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454758776487483849707953 2591069082365612887280965)
                      ·
                        rfl

theorem cell23_5046089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6, 2].length) (baseStart_5046089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046089 prefixEnd_5046089 := by exact prefixLift 5046089
  have htrace : WordTrace (prefixWord ++ tailWord_5046089) baseStart_5046089 baseEnd_5046089 := by
    simpa [prefixWord, tailWord_5046089, baseEnd_5046089] using wordTrace_append hprefix tailTrace_5046089
  have hstable : (prefixWord ++ tailWord_5046089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046089).length < 2 ^ (prefixWord ++ tailWord_5046089).sum := by decide
  have hdescent : baseEnd_5046089 < baseStart_5046089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046129 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 6]
def baseStart_5046129 : Nat := 118140960795 + 5046129 * 2 ^ 59
def prefixEnd_5046129 : Nat := 4983230072969 + 3 ^ 40 * 5046129 * 2
def baseEnd_5046129 : Nat := 287898846843532525642309

theorem tailTrace_5046129 : CollatzResearch.WordTrace tailWord_5046129 prefixEnd_5046129 287898846843532525642309 := by
  unfold tailWord_5046129
  simp only [CollatzResearch.WordTrace]
  refine ⟨184047444735743918066093441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122698296490495945377395627 184047444735743918066093441)
  ·
    refine ⟨138035583551807938549570081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184047444735743918066093441 138035583551807938549570081)
    ·
      refine ⟨103526687663855953912177561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138035583551807938549570081 103526687663855953912177561)
      ·
        refine ⟨77645015747891965434133171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103526687663855953912177561 77645015747891965434133171)
        ·
          refine ⟨116467523621837948151199757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77645015747891965434133171 116467523621837948151199757)
          ·
            refine ⟨43675321358189230556699909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116467523621837948151199757 43675321358189230556699909)
            ·
              refine ⟨8189122754660480729381233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43675321358189230556699909 8189122754660480729381233)
              ·
                refine ⟨6141842065995360547035925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8189122754660480729381233 6141842065995360547035925)
                ·
                  refine ⟨287898846843532525642309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6141842065995360547035925 287898846843532525642309)
                  ·
                    rfl

theorem cell23_5046129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_5046129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046129 prefixEnd_5046129 := by exact prefixLift 5046129
  have htrace : WordTrace (prefixWord ++ tailWord_5046129) baseStart_5046129 baseEnd_5046129 := by
    simpa [prefixWord, tailWord_5046129, baseEnd_5046129] using wordTrace_append hprefix tailTrace_5046129
  have hstable : (prefixWord ++ tailWord_5046129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046129).length < 2 ^ (prefixWord ++ tailWord_5046129).sum := by decide
  have hdescent : baseEnd_5046129 < baseStart_5046129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046133 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5046133 : Nat := 118140960795 + 5046133 * 2 ^ 59
def prefixEnd_5046133 : Nat := 4983230072969 + 3 ^ 40 * 5046133 * 2
def baseEnd_5046133 : Nat := 863697225171470238376921

theorem tailTrace_5046133 : CollatzResearch.WordTrace tailWord_5046133 prefixEnd_5046133 863697225171470238376921 := by
  unfold tailWord_5046133
  simp only [CollatzResearch.WordTrace]
  refine ⟨184047590627729426749239053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122698393751819617832826035 184047590627729426749239053)
  ·
    refine ⟨69017846485398535030964645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184047590627729426749239053 69017846485398535030964645)
    ·
      refine ⟨12940846216012225318305871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69017846485398535030964645 12940846216012225318305871)
      ·
        refine ⟨19411269324018337977458807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12940846216012225318305871 19411269324018337977458807)
        ·
          refine ⟨29116903986027506966188211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19411269324018337977458807 29116903986027506966188211)
          ·
            refine ⟨43675355979041260449282317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29116903986027506966188211 43675355979041260449282317)
            ·
              refine ⟨16378258492140472668480869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43675355979041260449282317 16378258492140472668480869)
              ·
                refine ⟨3070923467276338625340163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16378258492140472668480869 3070923467276338625340163)
                ·
                  refine ⟨4606385200914507938010245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3070923467276338625340163 4606385200914507938010245)
                  ·
                    refine ⟨863697225171470238376921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606385200914507938010245 863697225171470238376921)
                    ·
                      rfl

theorem cell23_5046133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5046133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046133 prefixEnd_5046133 := by exact prefixLift 5046133
  have htrace : WordTrace (prefixWord ++ tailWord_5046133) baseStart_5046133 baseEnd_5046133 := by
    simpa [prefixWord, tailWord_5046133, baseEnd_5046133] using wordTrace_append hprefix tailTrace_5046133
  have hstable : (prefixWord ++ tailWord_5046133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046133).length < 2 ^ (prefixWord ++ tailWord_5046133).sum := by decide
  have hdescent : baseEnd_5046133 < baseStart_5046133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046206 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_5046206 : Nat := 118140960795 + 5046206 * 2 ^ 59
def prefixEnd_5046206 : Nat := 4983230072969 + 3 ^ 40 * 5046206 * 2
def baseEnd_5046206 : Nat := 863709719867396309839309

theorem tailTrace_5046206 : CollatzResearch.WordTrace tailWord_5046206 prefixEnd_5046206 863709719867396309839309 := by
  unfold tailWord_5046206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23006281644558120027080809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122700168770976640144430981 23006281644558120027080809)
  ·
    refine ⟨17254711233418590020310607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23006281644558120027080809 17254711233418590020310607)
    ·
      refine ⟨25882066850127885030465911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17254711233418590020310607 25882066850127885030465911)
      ·
        refine ⟨38823100275191827545698867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882066850127885030465911 38823100275191827545698867)
        ·
          refine ⟨58234650412787741318548301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38823100275191827545698867 58234650412787741318548301)
          ·
            refine ⟨21837993904795402994455613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58234650412787741318548301 21837993904795402994455613)
            ·
              refine ⟨8189247714298276122920855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21837993904795402994455613 8189247714298276122920855)
              ·
                refine ⟨12283871571447414184381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8189247714298276122920855 12283871571447414184381283)
                ·
                  refine ⟨18425807357171121276571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12283871571447414184381283 18425807357171121276571925)
                  ·
                    refine ⟨863709719867396309839309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18425807357171121276571925 863709719867396309839309)
                    ·
                      rfl

theorem cell23_5046206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_5046206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046206 prefixEnd_5046206 := by exact prefixLift 5046206
  have htrace : WordTrace (prefixWord ++ tailWord_5046206) baseStart_5046206 baseEnd_5046206 := by
    simpa [prefixWord, tailWord_5046206, baseEnd_5046206] using wordTrace_append hprefix tailTrace_5046206
  have hstable : (prefixWord ++ tailWord_5046206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046206).length < 2 ^ (prefixWord ++ tailWord_5046206).sum := by decide
  have hdescent : baseEnd_5046206 < baseStart_5046206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046247 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5046247 : Nat := 118140960795 + 5046247 * 2 ^ 59
def prefixEnd_5046247 : Nat := 4983230072969 + 3 ^ 40 * 5046247 * 2
def baseEnd_5046247 : Nat := 2591150212309023269105239

theorem tailTrace_5046247 : CollatzResearch.WordTrace tailWord_5046247 prefixEnd_5046247 2591150212309023269105239 := by
  unfold tailWord_5046247
  simp only [CollatzResearch.WordTrace]
  refine ⟨184051748549316424218888995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122701165699544282812592663 184051748549316424218888995)
  ·
    refine ⟨276077622823974636328333493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184051748549316424218888995 276077622823974636328333493)
    ·
      refine ⟨25882277139747622155781265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 276077622823974636328333493 25882277139747622155781265)
      ·
        refine ⟨19411707854810716616835949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25882277139747622155781265 19411707854810716616835949)
        ·
          refine ⟨7279390445554018731313481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19411707854810716616835949 7279390445554018731313481)
          ·
            refine ⟨5459542834165514048485111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7279390445554018731313481 5459542834165514048485111)
            ·
              refine ⟨8189314251248271072727667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459542834165514048485111 8189314251248271072727667)
              ·
                refine ⟨12283971376872406609091501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8189314251248271072727667 12283971376872406609091501)
                ·
                  refine ⟨4606489266327152478409313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12283971376872406609091501 4606489266327152478409313)
                  ·
                    refine ⟨3454866949745364358806985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606489266327152478409313 3454866949745364358806985)
                    ·
                      refine ⟨2591150212309023269105239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454866949745364358806985 2591150212309023269105239)
                      ·
                        rfl

theorem cell23_5046247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5046247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046247 prefixEnd_5046247 := by exact prefixLift 5046247
  have htrace : WordTrace (prefixWord ++ tailWord_5046247) baseStart_5046247 baseEnd_5046247 := by
    simpa [prefixWord, tailWord_5046247, baseEnd_5046247] using wordTrace_append hprefix tailTrace_5046247
  have hstable : (prefixWord ++ tailWord_5046247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046247).length < 2 ^ (prefixWord ++ tailWord_5046247).sum := by decide
  have hdescent : baseEnd_5046247 < baseStart_5046247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046253 : List Nat := [1, 5, 1, 4, 1, 1, 2, 8]
def baseStart_5046253 : Nat := 118140960795 + 5046253 * 2 ^ 59
def prefixEnd_5046253 : Nat := 4983230072969 + 3 ^ 40 * 5046253 * 2
def baseEnd_5046253 : Nat := 95968640488627786875193

theorem tailTrace_5046253 : CollatzResearch.WordTrace tailWord_5046253 prefixEnd_5046253 95968640488627786875193 := by
  unfold tailWord_5046253
  simp only [CollatzResearch.WordTrace]
  refine ⟨184051967387294687243607413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122701311591529791495738275 184051967387294687243607413)
  ·
    refine ⟨17254871942558876929088195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184051967387294687243607413 17254871942558876929088195)
    ·
      refine ⟨25882307913838315393632293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17254871942558876929088195 25882307913838315393632293)
      ·
        refine ⟨4852932733844684136306055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25882307913838315393632293 4852932733844684136306055)
        ·
          refine ⟨7279399100767026204459083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4852932733844684136306055 7279399100767026204459083)
          ·
            refine ⟨10919098651150539306688625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7279399100767026204459083 10919098651150539306688625)
            ·
              refine ⟨8189323988362904480016469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10919098651150539306688625 8189323988362904480016469)
              ·
                refine ⟨95968640488627786875193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8189323988362904480016469 95968640488627786875193)
                ·
                  rfl

theorem cell23_5046253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 8].length) (baseStart_5046253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046253 prefixEnd_5046253 := by exact prefixLift 5046253
  have htrace : WordTrace (prefixWord ++ tailWord_5046253) baseStart_5046253 baseEnd_5046253 := by
    simpa [prefixWord, tailWord_5046253, baseEnd_5046253] using wordTrace_append hprefix tailTrace_5046253
  have hstable : (prefixWord ++ tailWord_5046253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046253).length < 2 ^ (prefixWord ++ tailWord_5046253).sum := by decide
  have hdescent : baseEnd_5046253 < baseStart_5046253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046257 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 2, 4]
def baseStart_5046257 : Nat := 118140960795 + 5046257 * 2 ^ 59
def prefixEnd_5046257 : Nat := 4983230072969 + 3 ^ 40 * 5046257 * 2
def baseEnd_5046257 : Nat := 863718449038522743326731

theorem tailTrace_5046257 : CollatzResearch.WordTrace tailWord_5046257 prefixEnd_5046257 863718449038522743326731 := by
  unfold tailWord_5046257
  simp only [CollatzResearch.WordTrace]
  refine ⟨184052113279280195926753025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122701408852853463951168683 184052113279280195926753025)
  ·
    refine ⟨138039084959460146945064769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184052113279280195926753025 138039084959460146945064769)
    ·
      refine ⟨103529313719595110208798577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138039084959460146945064769 103529313719595110208798577)
      ·
        refine ⟨77646985289696332656598933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103529313719595110208798577 77646985289696332656598933)
        ·
          refine ⟨3639702435454515593278075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77646985289696332656598933 3639702435454515593278075)
          ·
            refine ⟨5459553653181773389917113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639702435454515593278075 5459553653181773389917113)
            ·
              refine ⟨4094665239886330042437835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459553653181773389917113 4094665239886330042437835)
              ·
                refine ⟨6141997859829495063656753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094665239886330042437835 6141997859829495063656753)
                ·
                  refine ⟨4606498394872121297742565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6141997859829495063656753 4606498394872121297742565)
                  ·
                    refine ⟨863718449038522743326731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606498394872121297742565 863718449038522743326731)
                    ·
                      rfl

theorem cell23_5046257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_5046257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046257 prefixEnd_5046257 := by exact prefixLift 5046257
  have htrace : WordTrace (prefixWord ++ tailWord_5046257) baseStart_5046257 baseEnd_5046257 := by
    simpa [prefixWord, tailWord_5046257, baseEnd_5046257] using wordTrace_append hprefix tailTrace_5046257
  have hstable : (prefixWord ++ tailWord_5046257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046257).length < 2 ^ (prefixWord ++ tailWord_5046257).sum := by decide
  have hdescent : baseEnd_5046257 < baseStart_5046257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046273 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_5046273 : Nat := 118140960795 + 5046273 * 2 ^ 59
def prefixEnd_5046273 : Nat := 4983230072969 + 3 ^ 40 * 5046273 * 2
def baseEnd_5046273 : Nat := 2591163562806040167380119

theorem tailTrace_5046273 : CollatzResearch.WordTrace tailWord_5046273 prefixEnd_5046273 2591163562806040167380119 := by
  unfold tailWord_5046273
  simp only [CollatzResearch.WordTrace]
  refine ⟨184052696847222230659335473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122701797898148153772890315 184052696847222230659335473)
  ·
    refine ⟨138039522635416672994501605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184052696847222230659335473 138039522635416672994501605)
    ·
      refine ⟨25882410494140626186469051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138039522635416672994501605 25882410494140626186469051)
      ·
        refine ⟨38823615741210939279703577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882410494140626186469051 38823615741210939279703577)
        ·
          refine ⟨29117711805908204459777683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38823615741210939279703577 29117711805908204459777683)
          ·
            refine ⟨43676567708862306689666525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29117711805908204459777683 43676567708862306689666525)
            ·
              refine ⟨16378712890823365008624947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43676567708862306689666525 16378712890823365008624947)
              ·
                refine ⟨24568069336235047512937421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16378712890823365008624947 24568069336235047512937421)
                ·
                  refine ⟨9213026001088142817351533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24568069336235047512937421 9213026001088142817351533)
                  ·
                    refine ⟨3454884750408053556506825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9213026001088142817351533 3454884750408053556506825)
                    ·
                      refine ⟨2591163562806040167380119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454884750408053556506825 2591163562806040167380119)
                      ·
                        rfl

theorem cell23_5046273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_5046273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046273 prefixEnd_5046273 := by exact prefixLift 5046273
  have htrace : WordTrace (prefixWord ++ tailWord_5046273) baseStart_5046273 baseEnd_5046273 := by
    simpa [prefixWord, tailWord_5046273, baseEnd_5046273] using wordTrace_append hprefix tailTrace_5046273
  have hstable : (prefixWord ++ tailWord_5046273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046273).length < 2 ^ (prefixWord ++ tailWord_5046273).sum := by decide
  have hdescent : baseEnd_5046273 < baseStart_5046273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046306 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_5046306 : Nat := 118140960795 + 5046306 * 2 ^ 59
def prefixEnd_5046306 : Nat := 4983230072969 + 3 ^ 40 * 5046306 * 2
def baseEnd_5046306 : Nat := 2591180507667638538267467

theorem tailTrace_5046306 : CollatzResearch.WordTrace tailWord_5046306 prefixEnd_5046306 2591180507667638538267467 := by
  unfold tailWord_5046306
  simp only [CollatzResearch.WordTrace]
  refine ⟨46013475114025669323821693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122702600304068451530191181 46013475114025669323821693)
  ·
    refine ⟨17255053167759625996433135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46013475114025669323821693 17255053167759625996433135)
    ·
      refine ⟨25882579751639438994649703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17255053167759625996433135 25882579751639438994649703)
      ·
        refine ⟨38823869627459158491974555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882579751639438994649703 38823869627459158491974555)
        ·
          refine ⟨58235804441188737737961833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38823869627459158491974555 58235804441188737737961833)
          ·
            refine ⟨43676853330891553303471375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58235804441188737737961833 43676853330891553303471375)
            ·
              refine ⟨65515279996337329955207063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43676853330891553303471375 65515279996337329955207063)
              ·
                refine ⟨98272919994505994932810595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65515279996337329955207063 98272919994505994932810595)
                ·
                  refine ⟨147409379991758992399215893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98272919994505994932810595 147409379991758992399215893)
                  ·
                    refine ⟨6909814687113702768713245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147409379991758992399215893 6909814687113702768713245)
                    ·
                      refine ⟨2591180507667638538267467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6909814687113702768713245 2591180507667638538267467)
                      ·
                        rfl

theorem cell23_5046306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_5046306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046306 prefixEnd_5046306 := by exact prefixLift 5046306
  have htrace : WordTrace (prefixWord ++ tailWord_5046306) baseStart_5046306 baseEnd_5046306 := by
    simpa [prefixWord, tailWord_5046306, baseEnd_5046306] using wordTrace_append hprefix tailTrace_5046306
  have hstable : (prefixWord ++ tailWord_5046306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046306).length < 2 ^ (prefixWord ++ tailWord_5046306).sum := by decide
  have hdescent : baseEnd_5046306 < baseStart_5046306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046320 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2]
def baseStart_5046320 : Nat := 118140960795 + 5046320 * 2 ^ 59
def prefixEnd_5046320 : Nat := 4983230072969 + 3 ^ 40 * 5046320 * 2
def baseEnd_5046320 : Nat := 2591187696396801483492403

theorem tailTrace_5046320 : CollatzResearch.WordTrace tailWord_5046320 prefixEnd_5046320 2591187696396801483492403 := by
  unfold tailWord_5046320
  simp only [CollatzResearch.WordTrace]
  refine ⟨92027205539025978843148207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122702940718701305124197609 92027205539025978843148207)
  ·
    refine ⟨138040808308538968264722311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92027205539025978843148207 138040808308538968264722311)
    ·
      refine ⟨207061212462808452397083467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138040808308538968264722311 207061212462808452397083467)
      ·
        refine ⟨310591818694212678595625201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207061212462808452397083467 310591818694212678595625201)
        ·
          refine ⟨232943864020659508946718901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310591818694212678595625201 232943864020659508946718901)
          ·
            refine ⟨21838487251936828963754897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232943864020659508946718901 21838487251936828963754897)
            ·
              refine ⟨16378865438952621722816173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21838487251936828963754897 16378865438952621722816173)
              ·
                refine ⟨6142074539607233146056065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16378865438952621722816173 6142074539607233146056065)
                ·
                  refine ⟨4606555904705424859542049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142074539607233146056065 4606555904705424859542049)
                  ·
                    refine ⟨3454916928529068644656537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606555904705424859542049 3454916928529068644656537)
                    ·
                      refine ⟨2591187696396801483492403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454916928529068644656537 2591187696396801483492403)
                      ·
                        rfl

theorem cell23_5046320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2].length) (baseStart_5046320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046320 prefixEnd_5046320 := by exact prefixLift 5046320
  have htrace : WordTrace (prefixWord ++ tailWord_5046320) baseStart_5046320 baseEnd_5046320 := by
    simpa [prefixWord, tailWord_5046320, baseEnd_5046320] using wordTrace_append hprefix tailTrace_5046320
  have hstable : (prefixWord ++ tailWord_5046320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046320).length < 2 ^ (prefixWord ++ tailWord_5046320).sum := by decide
  have hdescent : baseEnd_5046320 < baseStart_5046320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046343 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 5]
def baseStart_5046343 : Nat := 118140960795 + 5046343 * 2 ^ 59
def prefixEnd_5046343 : Nat := 4983230072969 + 3 ^ 40 * 5046343 * 2
def baseEnd_5046343 : Nat := 287911056272428321500533

theorem tailTrace_5046343 : CollatzResearch.WordTrace tailWord_5046343 prefixEnd_5046343 287911056272428321500533 := by
  unfold tailWord_5046343
  simp only [CollatzResearch.WordTrace]
  refine ⟨184055249956968632614383683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122703499971312421742922455 184055249956968632614383683)
  ·
    refine ⟨276082874935452948921575525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184055249956968632614383683 276082874935452948921575525)
    ·
      refine ⟨51765539050397427922795411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276082874935452948921575525 51765539050397427922795411)
      ·
        refine ⟨77648308575596141884193117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51765539050397427922795411 77648308575596141884193117)
        ·
          refine ⟨29118115715848553206572419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77648308575596141884193117 29118115715848553206572419)
          ·
            refine ⟨43677173573772829809858629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29118115715848553206572419 43677173573772829809858629)
            ·
              refine ⟨8189470045082405589348493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43677173573772829809858629 8189470045082405589348493)
              ·
                refine ⟨3071051266905902096005685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8189470045082405589348493 3071051266905902096005685)
                ·
                  refine ⟨287911056272428321500533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3071051266905902096005685 287911056272428321500533)
                  ·
                    rfl

theorem cell23_5046343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 5].length) (baseStart_5046343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046343 prefixEnd_5046343 := by exact prefixLift 5046343
  have htrace : WordTrace (prefixWord ++ tailWord_5046343) baseStart_5046343 baseEnd_5046343 := by
    simpa [prefixWord, tailWord_5046343, baseEnd_5046343] using wordTrace_append hprefix tailTrace_5046343
  have hstable : (prefixWord ++ tailWord_5046343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046343).length < 2 ^ (prefixWord ++ tailWord_5046343).sum := by decide
  have hdescent : baseEnd_5046343 < baseStart_5046343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046354 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_5046354 : Nat := 118140960795 + 5046354 * 2 ^ 59
def prefixEnd_5046354 : Nat := 4983230072969 + 3 ^ 40 * 5046354 * 2
def baseEnd_5046354 : Nat := 2591205154739054350467247

theorem tailTrace_5046354 : CollatzResearch.WordTrace tailWord_5046354 prefixEnd_5046354 2591205154739054350467247 := by
  unfold tailWord_5046354
  simp only [CollatzResearch.WordTrace]
  refine ⟨46013912789982195373258529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122703767439952520995356077 46013912789982195373258529)
  ·
    refine ⟨34510434592486646529943897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46013912789982195373258529 34510434592486646529943897)
    ·
      refine ⟨25882825944364984897457923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34510434592486646529943897 25882825944364984897457923)
      ·
        refine ⟨38824238916547477346186885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882825944364984897457923 38824238916547477346186885)
        ·
          refine ⟨7279544796852652002410041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38824238916547477346186885 7279544796852652002410041)
          ·
            refine ⟨5459658597639489001807531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7279544796852652002410041 5459658597639489001807531)
            ·
              refine ⟨8189487896459233502711297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459658597639489001807531 8189487896459233502711297)
              ·
                refine ⟨6142115922344425127033473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8189487896459233502711297 6142115922344425127033473)
                ·
                  refine ⟨4606586941758318845275105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142115922344425127033473 4606586941758318845275105)
                  ·
                    refine ⟨3454940206318739133956329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606586941758318845275105 3454940206318739133956329)
                    ·
                      refine ⟨2591205154739054350467247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454940206318739133956329 2591205154739054350467247)
                      ·
                        rfl

theorem cell23_5046354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_5046354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046354 prefixEnd_5046354 := by exact prefixLift 5046354
  have htrace : WordTrace (prefixWord ++ tailWord_5046354) baseStart_5046354 baseEnd_5046354 := by
    simpa [prefixWord, tailWord_5046354, baseEnd_5046354] using wordTrace_append hprefix tailTrace_5046354
  have hstable : (prefixWord ++ tailWord_5046354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046354).length < 2 ^ (prefixWord ++ tailWord_5046354).sum := by decide
  have hdescent : baseEnd_5046354 < baseStart_5046354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046356 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_5046356 : Nat := 118140960795 + 5046356 * 2 ^ 59
def prefixEnd_5046356 : Nat := 4983230072969 + 3 ^ 40 * 5046356 * 2
def baseEnd_5046356 : Nat := 863735393900121114214079

theorem tailTrace_5046356 : CollatzResearch.WordTrace tailWord_5046356 prefixEnd_5046356 863735393900121114214079 := by
  unfold tailWord_5046356
  simp only [CollatzResearch.WordTrace]
  refine ⟨92027862052960767917303461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122703816070614357223071281 92027862052960767917303461)
  ·
    refine ⟨17255224134930143984494399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92027862052960767917303461 17255224134930143984494399)
    ·
      refine ⟨25882836202395215976741599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17255224134930143984494399 25882836202395215976741599)
      ·
        refine ⟨38824254303592823965112399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25882836202395215976741599 38824254303592823965112399)
        ·
          refine ⟨58236381455389235947668599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38824254303592823965112399 58236381455389235947668599)
          ·
            refine ⟨87354572183083853921502899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58236381455389235947668599 87354572183083853921502899)
            ·
              refine ⟨131031858274625780882254349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87354572183083853921502899 131031858274625780882254349)
              ·
                refine ⟨49136946852984667830845381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131031858274625780882254349 49136946852984667830845381)
                ·
                  refine ⟨9213177534934625218283509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49136946852984667830845381 9213177534934625218283509)
                  ·
                    refine ⟨863735393900121114214079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9213177534934625218283509 863735393900121114214079)
                    ·
                      rfl

theorem cell23_5046356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_5046356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046356 prefixEnd_5046356 := by exact prefixLift 5046356
  have htrace : WordTrace (prefixWord ++ tailWord_5046356) baseStart_5046356 baseEnd_5046356 := by
    simpa [prefixWord, tailWord_5046356, baseEnd_5046356] using wordTrace_append hprefix tailTrace_5046356
  have hstable : (prefixWord ++ tailWord_5046356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046356).length < 2 ^ (prefixWord ++ tailWord_5046356).sum := by decide
  have hdescent : baseEnd_5046356 < baseStart_5046356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046416 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 6]
def baseStart_5046416 : Nat := 118140960795 + 5046416 * 2 ^ 59
def prefixEnd_5046416 : Nat := 4983230072969 + 3 ^ 40 * 5046416 * 2
def baseEnd_5046416 : Nat := 287915221171070345321329

theorem tailTrace_5046416 : CollatzResearch.WordTrace tailWord_5046416 prefixEnd_5046416 287915221171070345321329 := by
  unfold tailWord_5046416
  simp only [CollatzResearch.WordTrace]
  refine ⟨92028956242852083040895551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122705274990469444054527401 92028956242852083040895551)
  ·
    refine ⟨138043434364278124561343327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92028956242852083040895551 138043434364278124561343327)
    ·
      refine ⟨207065151546417186842014991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138043434364278124561343327 207065151546417186842014991)
      ·
        refine ⟨310597727319625780263022487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207065151546417186842014991 310597727319625780263022487)
        ·
          refine ⟨465896590979438670394533731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310597727319625780263022487 465896590979438670394533731)
          ·
            refine ⟨698844886469158005591800597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465896590979438670394533731 698844886469158005591800597)
            ·
              refine ⟨32758354053241781512115653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 698844886469158005591800597 32758354053241781512115653)
              ·
                refine ⟨6142191384982834033521685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32758354053241781512115653 6142191384982834033521685)
                ·
                  refine ⟨287915221171070345321329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6142191384982834033521685 287915221171070345321329)
                  ·
                    rfl

theorem cell23_5046416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_5046416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046416 prefixEnd_5046416 := by exact prefixLift 5046416
  have htrace : WordTrace (prefixWord ++ tailWord_5046416) baseStart_5046416 baseEnd_5046416 := by
    simpa [prefixWord, tailWord_5046416, baseEnd_5046416] using wordTrace_append hprefix tailTrace_5046416
  have hstable : (prefixWord ++ tailWord_5046416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046416).length < 2 ^ (prefixWord ++ tailWord_5046416).sum := by decide
  have hdescent : baseEnd_5046416 < baseStart_5046416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046422 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5046422 : Nat := 118140960795 + 5046422 * 2 ^ 59
def prefixEnd_5046422 : Nat := 4983230072969 + 3 ^ 40 * 5046422 * 2
def baseEnd_5046422 : Nat := 2591240071423560084416935

theorem tailTrace_5046422 : CollatzResearch.WordTrace tailWord_5046422 prefixEnd_5046422 2591240071423560084416935 := by
  unfold tailWord_5046422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11503633207730151819156845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122705420882454952737673013 11503633207730151819156845)
  ·
    refine ⟨4313862452898806932183817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11503633207730151819156845 4313862452898806932183817)
    ·
      refine ⟨3235396839674105199137863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4313862452898806932183817 3235396839674105199137863)
      ·
        refine ⟨4853095259511157798706795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235396839674105199137863 4853095259511157798706795)
        ·
          refine ⟨7279642889266736698060193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4853095259511157798706795 7279642889266736698060193)
          ·
            refine ⟨5459732166950052523545145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7279642889266736698060193 5459732166950052523545145)
            ·
              refine ⟨4094799125212539392658859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459732166950052523545145 4094799125212539392658859)
              ·
                refine ⟨6142198687818809088988289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4094799125212539392658859 6142198687818809088988289)
                ·
                  refine ⟨4606649015864106816741217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6142198687818809088988289 4606649015864106816741217)
                  ·
                    refine ⟨3454986761898080112555913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606649015864106816741217 3454986761898080112555913)
                    ·
                      refine ⟨2591240071423560084416935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3454986761898080112555913 2591240071423560084416935)
                      ·
                        rfl

theorem cell23_5046422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5046422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046422 prefixEnd_5046422 := by exact prefixLift 5046422
  have htrace : WordTrace (prefixWord ++ tailWord_5046422) baseStart_5046422 baseEnd_5046422 := by
    simpa [prefixWord, tailWord_5046422, baseEnd_5046422] using wordTrace_append hprefix tailTrace_5046422
  have hstable : (prefixWord ++ tailWord_5046422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046422).length < 2 ^ (prefixWord ++ tailWord_5046422).sum := by decide
  have hdescent : baseEnd_5046422 < baseStart_5046422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046433 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 6]
def baseStart_5046433 : Nat := 118140960795 + 5046433 * 2 ^ 59
def prefixEnd_5046433 : Nat := 4983230072969 + 3 ^ 40 * 5046433 * 2
def baseEnd_5046433 : Nat := 287916191078973282375487

theorem tailTrace_5046433 : CollatzResearch.WordTrace tailWord_5046433 prefixEnd_5046433 287916191078973282375487 := by
  unfold tailWord_5046433
  simp only [CollatzResearch.WordTrace]
  refine ⟨184058532526642577985159953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122705688351095051990106635 184058532526642577985159953)
  ·
    refine ⟨138043899394981933488869965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184058532526642577985159953 138043899394981933488869965)
    ·
      refine ⟨51766462273118225058326237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138043899394981933488869965 51766462273118225058326237)
      ·
        refine ⟨19412423352419334396872339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51766462273118225058326237 19412423352419334396872339)
        ·
          refine ⟨29118635028629001595308509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19412423352419334396872339 29118635028629001595308509)
          ·
            refine ⟨10919488135735875598240691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29118635028629001595308509 10919488135735875598240691)
            ·
              refine ⟨16379232203603813397361037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10919488135735875598240691 16379232203603813397361037)
              ·
                refine ⟨6142212076351430024010389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16379232203603813397361037 6142212076351430024010389)
                ·
                  refine ⟨287916191078973282375487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6142212076351430024010389 287916191078973282375487)
                  ·
                    rfl

theorem cell23_5046433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_5046433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046433 prefixEnd_5046433 := by exact prefixLift 5046433
  have htrace : WordTrace (prefixWord ++ tailWord_5046433) baseStart_5046433 baseEnd_5046433 := by
    simpa [prefixWord, tailWord_5046433, baseEnd_5046433] using wordTrace_append hprefix tailTrace_5046433
  have hstable : (prefixWord ++ tailWord_5046433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046433).length < 2 ^ (prefixWord ++ tailWord_5046433).sum := by decide
  have hdescent : baseEnd_5046433 < baseStart_5046433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046498 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5046498 : Nat := 118140960795 + 5046498 * 2 ^ 59
def prefixEnd_5046498 : Nat := 4983230072969 + 3 ^ 40 * 5046498 * 2
def baseEnd_5046498 : Nat := 2591279095953301787066585

theorem tailTrace_5046498 : CollatzResearch.WordTrace tailWord_5046498 prefixEnd_5046498 2591279095953301787066585 := by
  unfold tailWord_5046498
  simp only [CollatzResearch.WordTrace]
  refine ⟨46015225817851773521569037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122707268847604729390850765 46015225817851773521569037)
  ·
    refine ⟨17255709681694415070588389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46015225817851773521569037 17255709681694415070588389)
    ·
      refine ⟨3235445565317702825735323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17255709681694415070588389 3235445565317702825735323)
      ·
        refine ⟨4853168347976554238602985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235445565317702825735323 4853168347976554238602985)
        ·
          refine ⟨3639876260982415678952239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853168347976554238602985 3639876260982415678952239)
          ·
            refine ⟨5459814391473623518428359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3639876260982415678952239 5459814391473623518428359)
            ·
              refine ⟨8189721587210435277642539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459814391473623518428359 8189721587210435277642539)
              ·
                refine ⟨12284582380815652916463809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8189721587210435277642539 12284582380815652916463809)
                ·
                  refine ⟨9213436785611739687347857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12284582380815652916463809 9213436785611739687347857)
                  ·
                    refine ⟨6910077589208804765510893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9213436785611739687347857 6910077589208804765510893)
                    ·
                      refine ⟨2591279095953301787066585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910077589208804765510893 2591279095953301787066585)
                      ·
                        rfl

theorem cell23_5046498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5046498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046498 prefixEnd_5046498 := by exact prefixLift 5046498
  have htrace : WordTrace (prefixWord ++ tailWord_5046498) baseStart_5046498 baseEnd_5046498 := by
    simpa [prefixWord, tailWord_5046498, baseEnd_5046498] using wordTrace_append hprefix tailTrace_5046498
  have hstable : (prefixWord ++ tailWord_5046498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046498).length < 2 ^ (prefixWord ++ tailWord_5046498).sum := by decide
  have hdescent : baseEnd_5046498 < baseStart_5046498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046513 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_5046513 : Nat := 118140960795 + 5046513 * 2 ^ 59
def prefixEnd_5046513 : Nat := 4983230072969 + 3 ^ 40 * 5046513 * 2
def baseEnd_5046513 : Nat := 2591286798163119228379015

theorem tailTrace_5046513 : CollatzResearch.WordTrace tailWord_5046513 prefixEnd_5046513 2591286798163119228379015 := by
  unfold tailWord_5046513
  simp only [CollatzResearch.WordTrace]
  refine ⟨184061450366352751648072193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122707633577568501098714795 184061450366352751648072193)
  ·
    refine ⟨138046087774764563736054145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184061450366352751648072193 138046087774764563736054145)
    ·
      refine ⟨103534565831073422802040609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138046087774764563736054145 103534565831073422802040609)
      ·
        refine ⟨77650924373305067101530457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103534565831073422802040609 77650924373305067101530457)
        ·
          refine ⟨58238193279978800326147843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77650924373305067101530457 58238193279978800326147843)
          ·
            refine ⟨87357289919968200489221765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58238193279978800326147843 87357289919968200489221765)
            ·
              refine ⟨16379491859994037591729081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87357289919968200489221765 16379491859994037591729081)
              ·
                refine ⟨12284618894995528193796811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16379491859994037591729081 12284618894995528193796811)
                ·
                  refine ⟨18426928342493292290695217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12284618894995528193796811 18426928342493292290695217)
                  ·
                    refine ⟨13820196256869969218021413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18426928342493292290695217 13820196256869969218021413)
                    ·
                      refine ⟨2591286798163119228379015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13820196256869969218021413 2591286798163119228379015)
                      ·
                        rfl

theorem cell23_5046513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_5046513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046513 prefixEnd_5046513 := by exact prefixLift 5046513
  have htrace : WordTrace (prefixWord ++ tailWord_5046513) baseStart_5046513 baseEnd_5046513 := by
    simpa [prefixWord, tailWord_5046513, baseEnd_5046513] using wordTrace_append hprefix tailTrace_5046513
  have hstable : (prefixWord ++ tailWord_5046513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046513).length < 2 ^ (prefixWord ++ tailWord_5046513).sum := by decide
  have hdescent : baseEnd_5046513 < baseStart_5046513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046557 : List Nat := [1, 4, 2, 3, 2, 2, 2, 7]
def baseStart_5046557 : Nat := 118140960795 + 5046557 * 2 ^ 59
def prefixEnd_5046557 : Nat := 4983230072969 + 3 ^ 40 * 5046557 * 2
def baseEnd_5046557 : Nat := 95974421900441372452919

theorem tailTrace_5046557 : CollatzResearch.WordTrace tailWord_5046557 prefixEnd_5046557 95974421900441372452919 := by
  unfold tailWord_5046557
  simp only [CollatzResearch.WordTrace]
  refine ⟨184063055178193347162673925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122708703452128898108449283 184063055178193347162673925)
  ·
    refine ⟨34511822845911252593001361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184063055178193347162673925 34511822845911252593001361)
    ·
      refine ⟨25883867134433439444751021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34511822845911252593001361 25883867134433439444751021)
      ·
        refine ⟨9706450175412539791781633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25883867134433439444751021 9706450175412539791781633)
        ·
          refine ⟨7279837631559404843836225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9706450175412539791781633 7279837631559404843836225)
          ·
            refine ⟨5459878223669553632877169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7279837631559404843836225 5459878223669553632877169)
            ·
              refine ⟨4094908667752165224657877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5459878223669553632877169 4094908667752165224657877)
              ·
                refine ⟨95974421900441372452919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4094908667752165224657877 95974421900441372452919)
                ·
                  rfl

theorem cell23_5046557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 7].length) (baseStart_5046557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046557 prefixEnd_5046557 := by exact prefixLift 5046557
  have htrace : WordTrace (prefixWord ++ tailWord_5046557) baseStart_5046557 baseEnd_5046557 := by
    simpa [prefixWord, tailWord_5046557, baseEnd_5046557] using wordTrace_append hprefix tailTrace_5046557
  have hstable : (prefixWord ++ tailWord_5046557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046557).length < 2 ^ (prefixWord ++ tailWord_5046557).sum := by decide
  have hdescent : baseEnd_5046557 < baseStart_5046557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046568 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_5046568 : Nat := 118140960795 + 5046568 * 2 ^ 59
def prefixEnd_5046568 : Nat := 4983230072969 + 3 ^ 40 * 5046568 * 2
def baseEnd_5046568 : Nat := 2591315039599116513191263

theorem tailTrace_5046568 : CollatzResearch.WordTrace tailWord_5046568 prefixEnd_5046568 2591315039599116513191263 := by
  unfold tailWord_5046568
  simp only [CollatzResearch.WordTrace]
  refine ⟨92031728190576748020662179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122708970920768997360882905 92031728190576748020662179)
  ·
    refine ⟨138047592285865122030993269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92031728190576748020662179 138047592285865122030993269)
    ·
      refine ⟨12941961776799855190405619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138047592285865122030993269 12941961776799855190405619)
      ·
        refine ⟨19412942665199782785608429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12941961776799855190405619 19412942665199782785608429)
        ·
          refine ⟨7279853499449918544603161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19412942665199782785608429 7279853499449918544603161)
          ·
            refine ⟨5459890124587438908452371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7279853499449918544603161 5459890124587438908452371)
            ·
              refine ⟨8189835186881158362678557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459890124587438908452371 8189835186881158362678557)
              ·
                refine ⟨3071188195080434386004459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8189835186881158362678557 3071188195080434386004459)
                ·
                  refine ⟨4606782292620651579006689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071188195080434386004459 4606782292620651579006689)
                  ·
                    refine ⟨3455086719465488684255017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606782292620651579006689 3455086719465488684255017)
                    ·
                      refine ⟨2591315039599116513191263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455086719465488684255017 2591315039599116513191263)
                      ·
                        rfl

theorem cell23_5046568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_5046568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046568 prefixEnd_5046568 := by exact prefixLift 5046568
  have htrace : WordTrace (prefixWord ++ tailWord_5046568) baseStart_5046568 baseEnd_5046568 := by
    simpa [prefixWord, tailWord_5046568, baseEnd_5046568] using wordTrace_append hprefix tailTrace_5046568
  have hstable : (prefixWord ++ tailWord_5046568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046568).length < 2 ^ (prefixWord ++ tailWord_5046568).sum := by decide
  have hdescent : baseEnd_5046568 < baseStart_5046568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046657 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5046657 : Nat := 118140960795 + 5046657 * 2 ^ 59
def prefixEnd_5046657 : Nat := 4983230072969 + 3 ^ 40 * 5046657 * 2
def baseEnd_5046657 : Nat := 2591360739377366664978353

theorem tailTrace_5046657 : CollatzResearch.WordTrace tailWord_5046657 prefixEnd_5046657 2591360739377366664978353 := by
  unfold tailWord_5046657
  simp only [CollatzResearch.WordTrace]
  refine ⟨184066702477831064241314225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122711134985220709494209483 184066702477831064241314225)
  ·
    refine ⟨138050026858373298180985669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184066702477831064241314225 138050026858373298180985669)
    ·
      refine ⟨25884380035944993408934813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138050026858373298180985669 25884380035944993408934813)
      ·
        refine ⟨9706642513479372528350555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25884380035944993408934813 9706642513479372528350555)
        ·
          refine ⟨14559963770219058792525833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9706642513479372528350555 14559963770219058792525833)
          ·
            refine ⟨10919972827664294094394375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14559963770219058792525833 10919972827664294094394375)
            ·
              refine ⟨16379959241496441141591563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10919972827664294094394375 16379959241496441141591563)
              ·
                refine ⟨24569938862244661712387345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16379959241496441141591563 24569938862244661712387345)
                ·
                  refine ⟨18427454146683496284290509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24569938862244661712387345 18427454146683496284290509)
                  ·
                    refine ⟨6910295305006311106608941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18427454146683496284290509 6910295305006311106608941)
                    ·
                      refine ⟨2591360739377366664978353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910295305006311106608941 2591360739377366664978353)
                      ·
                        rfl

theorem cell23_5046657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5046657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046657 prefixEnd_5046657 := by exact prefixLift 5046657
  have htrace : WordTrace (prefixWord ++ tailWord_5046657) baseStart_5046657 baseEnd_5046657 := by
    simpa [prefixWord, tailWord_5046657, baseEnd_5046657] using wordTrace_append hprefix tailTrace_5046657
  have hstable : (prefixWord ++ tailWord_5046657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046657).length < 2 ^ (prefixWord ++ tailWord_5046657).sum := by decide
  have hdescent : baseEnd_5046657 < baseStart_5046657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046693 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_5046693 : Nat := 118140960795 + 5046693 * 2 ^ 59
def prefixEnd_5046693 : Nat := 4983230072969 + 3 ^ 40 * 5046693 * 2
def baseEnd_5046693 : Nat := 2591379224680928524128187

theorem tailTrace_5046693 : CollatzResearch.WordTrace tailWord_5046693 prefixEnd_5046693 2591379224680928524128187 := by
  unfold tailWord_5046693
  simp only [CollatzResearch.WordTrace]
  refine ⟨184068015505700642389624733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122712010337133761593083155 184068015505700642389624733)
  ·
    refine ⟨69025505814637740896109275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184068015505700642389624733 69025505814637740896109275)
    ·
      refine ⟨103538258721956611344163913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69025505814637740896109275 103538258721956611344163913)
      ·
        refine ⟨77653694041467458508122935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103538258721956611344163913 77653694041467458508122935)
        ·
          refine ⟨116480541062201187762184403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77653694041467458508122935 116480541062201187762184403)
          ·
            refine ⟨174720811593301781643276605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116480541062201187762184403 174720811593301781643276605)
            ·
              refine ⟨65520304347488168116228727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174720811593301781643276605 65520304347488168116228727)
              ·
                refine ⟨98280456521232252174343091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65520304347488168116228727 98280456521232252174343091)
                ·
                  refine ⟨147420684781848378261514637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98280456521232252174343091 147420684781848378261514637)
                  ·
                    refine ⟨55282756793193141848067989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147420684781848378261514637 55282756793193141848067989)
                    ·
                      refine ⟨2591379224680928524128187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55282756793193141848067989 2591379224680928524128187)
                      ·
                        rfl

theorem cell23_5046693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_5046693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046693 prefixEnd_5046693 := by exact prefixLift 5046693
  have htrace : WordTrace (prefixWord ++ tailWord_5046693) baseStart_5046693 baseEnd_5046693 := by
    simpa [prefixWord, tailWord_5046693, baseEnd_5046693] using wordTrace_append hprefix tailTrace_5046693
  have hstable : (prefixWord ++ tailWord_5046693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046693).length < 2 ^ (prefixWord ++ tailWord_5046693).sum := by decide
  have hdescent : baseEnd_5046693 < baseStart_5046693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046700 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_5046700 : Nat := 118140960795 + 5046700 * 2 ^ 59
def prefixEnd_5046700 : Nat := 4983230072969 + 3 ^ 40 * 5046700 * 2
def baseEnd_5046700 : Nat := 2591382819045509996740655

theorem tailTrace_5046700 : CollatzResearch.WordTrace tailWord_5046700 prefixEnd_5046700 2591382819045509996740655 := by
  unfold tailWord_5046700
  simp only [CollatzResearch.WordTrace]
  refine ⟨92034135408337641292564777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122712180544450188390086369 92034135408337641292564777)
  ·
    refine ⟨69025601556253230969423583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92034135408337641292564777 69025601556253230969423583)
    ·
      refine ⟨103538402334379846454135375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69025601556253230969423583 103538402334379846454135375)
      ·
        refine ⟨155307603501569769681203063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103538402334379846454135375 155307603501569769681203063)
        ·
          refine ⟨232961405252354654521804595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155307603501569769681203063 232961405252354654521804595)
          ·
            refine ⟨349442107878531981782706893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232961405252354654521804595 349442107878531981782706893)
            ·
              refine ⟨131040790454449493168515085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349442107878531981782706893 131040790454449493168515085)
              ·
                refine ⟨49140296420418559938193157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131040790454449493168515085 49140296420418559938193157)
                ·
                  refine ⟨9213805578828479988411217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49140296420418559938193157 9213805578828479988411217)
                  ·
                    refine ⟨6910354184121359991308413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9213805578828479988411217 6910354184121359991308413)
                    ·
                      refine ⟨2591382819045509996740655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910354184121359991308413 2591382819045509996740655)
                      ·
                        rfl

theorem cell23_5046700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_5046700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046700 prefixEnd_5046700 := by exact prefixLift 5046700
  have htrace : WordTrace (prefixWord ++ tailWord_5046700) baseStart_5046700 baseEnd_5046700 := by
    simpa [prefixWord, tailWord_5046700, baseEnd_5046700] using wordTrace_append hprefix tailTrace_5046700
  have hstable : (prefixWord ++ tailWord_5046700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046700).length < 2 ^ (prefixWord ++ tailWord_5046700).sum := by decide
  have hdescent : baseEnd_5046700 < baseStart_5046700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046723 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_5046723 : Nat := 118140960795 + 5046723 * 2 ^ 59
def prefixEnd_5046723 : Nat := 4983230072969 + 3 ^ 40 * 5046723 * 2
def baseEnd_5046723 : Nat := 2591394629100563406753049

theorem tailTrace_5046723 : CollatzResearch.WordTrace tailWord_5046723 prefixEnd_5046723 2591394629100563406753049 := by
  unfold tailWord_5046723
  simp only [CollatzResearch.WordTrace]
  refine ⟨184069109695591957513216823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122712739797061305008811215 184069109695591957513216823)
  ·
    refine ⟨276103664543387936269825235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184069109695591957513216823 276103664543387936269825235)
    ·
      refine ⟨414155496815081904404737853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276103664543387936269825235 414155496815081904404737853)
      ·
        refine ⟨155308311305655714151776695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414155496815081904404737853 155308311305655714151776695)
        ·
          refine ⟨232962466958483571227665043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155308311305655714151776695 232962466958483571227665043)
          ·
            refine ⟨349443700437725356841497565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232962466958483571227665043 349443700437725356841497565)
            ·
              refine ⟨131041387664147008815561587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349443700437725356841497565 131041387664147008815561587)
              ·
                refine ⟨196562081496220513223342381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131041387664147008815561587 196562081496220513223342381)
                ·
                  refine ⟨73710780561082692458753393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196562081496220513223342381 73710780561082692458753393)
                  ·
                    refine ⟨55283085420812019344065045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73710780561082692458753393 55283085420812019344065045)
                    ·
                      refine ⟨2591394629100563406753049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55283085420812019344065045 2591394629100563406753049)
                      ·
                        rfl

theorem cell23_5046723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_5046723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046723 prefixEnd_5046723 := by exact prefixLift 5046723
  have htrace : WordTrace (prefixWord ++ tailWord_5046723) baseStart_5046723 baseEnd_5046723 := by
    simpa [prefixWord, tailWord_5046723, baseEnd_5046723] using wordTrace_append hprefix tailTrace_5046723
  have hstable : (prefixWord ++ tailWord_5046723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046723).length < 2 ^ (prefixWord ++ tailWord_5046723).sum := by decide
  have hdescent : baseEnd_5046723 < baseStart_5046723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046730 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_5046730 : Nat := 118140960795 + 5046730 * 2 ^ 59
def prefixEnd_5046730 : Nat := 4983230072969 + 3 ^ 40 * 5046730 * 2
def baseEnd_5046730 : Nat := 2591398223465144879365517

theorem tailTrace_5046730 : CollatzResearch.WordTrace tailWord_5046730 prefixEnd_5046730 2591398223465144879365517 := by
  unfold tailWord_5046730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46017341251641649427180411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122712910004377731805814429 46017341251641649427180411)
  ·
    refine ⟨69026011877462474140770617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46017341251641649427180411 69026011877462474140770617)
    ·
      refine ⟨51769508908096855605577963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69026011877462474140770617 51769508908096855605577963)
      ·
        refine ⟨77654263362145283408366945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51769508908096855605577963 77654263362145283408366945)
        ·
          refine ⟨58240697521608962556275209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77654263362145283408366945 58240697521608962556275209)
          ·
            refine ⟨43680523141206721917206407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58240697521608962556275209 43680523141206721917206407)
            ·
              refine ⟨65520784711810082875809611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43680523141206721917206407 65520784711810082875809611)
              ·
                refine ⟨98281177067715124313714417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65520784711810082875809611 98281177067715124313714417)
                ·
                  refine ⟨73710882800786343235285813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98281177067715124313714417 73710882800786343235285813)
                  ·
                    refine ⟨6910395262573719678308045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73710882800786343235285813 6910395262573719678308045)
                    ·
                      refine ⟨2591398223465144879365517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910395262573719678308045 2591398223465144879365517)
                      ·
                        rfl

theorem cell23_5046730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_5046730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046730 prefixEnd_5046730 := by exact prefixLift 5046730
  have htrace : WordTrace (prefixWord ++ tailWord_5046730) baseStart_5046730 baseEnd_5046730 := by
    simpa [prefixWord, tailWord_5046730, baseEnd_5046730] using wordTrace_append hprefix tailTrace_5046730
  have hstable : (prefixWord ++ tailWord_5046730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046730).length < 2 ^ (prefixWord ++ tailWord_5046730).sum := by decide
  have hdescent : baseEnd_5046730 < baseStart_5046730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046741 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_5046741 : Nat := 118140960795 + 5046741 * 2 ^ 59
def prefixEnd_5046741 : Nat := 4983230072969 + 3 ^ 40 * 5046741 * 2
def baseEnd_5046741 : Nat := 863801290584114778775989

theorem tailTrace_5046741 : CollatzResearch.WordTrace tailWord_5046741 prefixEnd_5046741 863801290584114778775989 := by
  unfold tailWord_5046741
  simp only [CollatzResearch.WordTrace]
  refine ⟨184069766209526746587372077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122713177473017831058248051 184069766209526746587372077)
  ·
    refine ⟨69026162328572529970264529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184069766209526746587372077 69026162328572529970264529)
    ·
      refine ⟨51769621746429397477698397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69026162328572529970264529 51769621746429397477698397)
      ·
        refine ⟨19413608154911024054136899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51769621746429397477698397 19413608154911024054136899)
        ·
          refine ⟨29120412232366536081205349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19413608154911024054136899 29120412232366536081205349)
          ·
            refine ⟨5460077293568725515226003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29120412232366536081205349 5460077293568725515226003)
            ·
              refine ⟨8190115940353088272839005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460077293568725515226003 8190115940353088272839005)
              ·
                refine ⟨3071293477632408102314627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8190115940353088272839005 3071293477632408102314627)
                ·
                  refine ⟨4606940216448612153471941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071293477632408102314627 4606940216448612153471941)
                  ·
                    refine ⟨863801290584114778775989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606940216448612153471941 863801290584114778775989)
                    ·
                      rfl

theorem cell23_5046741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_5046741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046741 prefixEnd_5046741 := by exact prefixLift 5046741
  have htrace : WordTrace (prefixWord ++ tailWord_5046741) baseStart_5046741 baseEnd_5046741 := by
    simpa [prefixWord, tailWord_5046741, baseEnd_5046741] using wordTrace_append hprefix tailTrace_5046741
  have hstable : (prefixWord ++ tailWord_5046741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046741).length < 2 ^ (prefixWord ++ tailWord_5046741).sum := by decide
  have hdescent : baseEnd_5046741 < baseStart_5046741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046774 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_5046774 : Nat := 118140960795 + 5046774 * 2 ^ 59
def prefixEnd_5046774 : Nat := 4983230072969 + 3 ^ 40 * 5046774 * 2
def baseEnd_5046774 : Nat := 2591420816613942707215315

theorem tailTrace_5046774 : CollatzResearch.WordTrace tailWord_5046774 prefixEnd_5046774 2591420816613942707215315 := by
  unfold tailWord_5046774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504435613650449576457711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122713979878938128815548917 11504435613650449576457711)
  ·
    refine ⟨17256653420475674364686567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504435613650449576457711 17256653420475674364686567)
    ·
      refine ⟨25884980130713511547029851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17256653420475674364686567 25884980130713511547029851)
      ·
        refine ⟨38827470196070267320544777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25884980130713511547029851 38827470196070267320544777)
        ·
          refine ⟨29120602647052700490408583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38827470196070267320544777 29120602647052700490408583)
          ·
            refine ⟨43680903970579050735612875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29120602647052700490408583 43680903970579050735612875)
            ·
              refine ⟨65521355955868576103419313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43680903970579050735612875 65521355955868576103419313)
              ·
                refine ⟨49141016966901432077564485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65521355955868576103419313 49141016966901432077564485)
                ·
                  refine ⟨9213940681294018514543341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49141016966901432077564485 9213940681294018514543341)
                  ·
                    refine ⟨3455227755485256942953753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9213940681294018514543341 3455227755485256942953753)
                    ·
                      refine ⟨2591420816613942707215315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455227755485256942953753 2591420816613942707215315)
                      ·
                        rfl

theorem cell23_5046774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_5046774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046774 prefixEnd_5046774 := by exact prefixLift 5046774
  have htrace : WordTrace (prefixWord ++ tailWord_5046774) baseStart_5046774 baseEnd_5046774 := by
    simpa [prefixWord, tailWord_5046774, baseEnd_5046774] using wordTrace_append hprefix tailTrace_5046774
  have hstable : (prefixWord ++ tailWord_5046774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046774).length < 2 ^ (prefixWord ++ tailWord_5046774).sum := by decide
  have hdescent : baseEnd_5046774 < baseStart_5046774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046780 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_5046780 : Nat := 118140960795 + 5046780 * 2 ^ 59
def prefixEnd_5046780 : Nat := 4983230072969 + 3 ^ 40 * 5046780 * 2
def baseEnd_5046780 : Nat := 863807965832623227913429

theorem tailTrace_5046780 : CollatzResearch.WordTrace tailWord_5046780 prefixEnd_5046780 863807965832623227913429 := by
  unfold tailWord_5046780
  simp only [CollatzResearch.WordTrace]
  refine ⟨92035594328192728124020897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122714125770923637498694529 92035594328192728124020897)
  ·
    refine ⟨69026695746144546093015673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92035594328192728124020897 69026695746144546093015673)
    ·
      refine ⟨51770021809608409569761755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69026695746144546093015673 51770021809608409569761755)
      ·
        refine ⟨77655032714412614354642633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51770021809608409569761755 77655032714412614354642633)
        ·
          refine ⟨58241274535809460765981975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77655032714412614354642633 58241274535809460765981975)
          ·
            refine ⟨87361911803714191148972963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58241274535809460765981975 87361911803714191148972963)
            ·
              refine ⟨131042867705571286723459445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87361911803714191148972963 131042867705571286723459445)
              ·
                refine ⟨12285268847397308130324323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131042867705571286723459445 12285268847397308130324323)
                ·
                  refine ⟨18427903271095962195486485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12285268847397308130324323 18427903271095962195486485)
                  ·
                    refine ⟨863807965832623227913429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18427903271095962195486485 863807965832623227913429)
                    ·
                      rfl

theorem cell23_5046780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_5046780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046780 prefixEnd_5046780 := by exact prefixLift 5046780
  have htrace : WordTrace (prefixWord ++ tailWord_5046780) baseStart_5046780 baseEnd_5046780 := by
    simpa [prefixWord, tailWord_5046780, baseEnd_5046780] using wordTrace_append hprefix tailTrace_5046780
  have hstable : (prefixWord ++ tailWord_5046780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046780).length < 2 ^ (prefixWord ++ tailWord_5046780).sum := by decide
  have hdescent : baseEnd_5046780 < baseStart_5046780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046791 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5046791 : Nat := 118140960795 + 5046791 * 2 ^ 59
def prefixEnd_5046791 : Nat := 4983230072969 + 3 ^ 40 * 5046791 * 2
def baseEnd_5046791 : Nat := 2591429545785069140702737

theorem tailTrace_5046791 : CollatzResearch.WordTrace tailWord_5046791 prefixEnd_5046791 2591429545785069140702737 := by
  unfold tailWord_5046791
  simp only [CollatzResearch.WordTrace]
  refine ⟨184071589859345605126692227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122714393239563736751128151 184071589859345605126692227)
  ·
    refine ⟨276107384789018407690038341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184071589859345605126692227 276107384789018407690038341)
    ·
      refine ⟨51770134647940951441882189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276107384789018407690038341 51770134647940951441882189)
      ·
        refine ⟨19413800492977856790705821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51770134647940951441882189 19413800492977856790705821)
        ·
          refine ⟨7280175184866696296514683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19413800492977856790705821 7280175184866696296514683)
          ·
            refine ⟨10920262777300044444772025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280175184866696296514683 10920262777300044444772025)
            ·
              refine ⟨8190197082975033333579019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10920262777300044444772025 8190197082975033333579019)
              ·
                refine ⟨12285295624462550000368529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190197082975033333579019 12285295624462550000368529)
                ·
                  refine ⟨9213971718346912500276397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12285295624462550000368529 9213971718346912500276397)
                  ·
                    refine ⟨3455239394380092187603649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9213971718346912500276397 3455239394380092187603649)
                    ·
                      refine ⟨2591429545785069140702737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455239394380092187603649 2591429545785069140702737)
                      ·
                        rfl

theorem cell23_5046791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5046791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046791 prefixEnd_5046791 := by exact prefixLift 5046791
  have htrace : WordTrace (prefixWord ++ tailWord_5046791) baseStart_5046791 baseEnd_5046791 := by
    simpa [prefixWord, tailWord_5046791, baseEnd_5046791] using wordTrace_append hprefix tailTrace_5046791
  have hstable : (prefixWord ++ tailWord_5046791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046791).length < 2 ^ (prefixWord ++ tailWord_5046791).sum := by decide
  have hdescent : baseEnd_5046791 < baseStart_5046791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046824 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5046824 : Nat := 118140960795 + 5046824 * 2 ^ 59
def prefixEnd_5046824 : Nat := 4983230072969 + 3 ^ 40 * 5046824 * 2
def baseEnd_5046824 : Nat := 2591446490646667511590085

theorem tailTrace_5046824 : CollatzResearch.WordTrace tailWord_5046824 prefixEnd_5046824 2591446490646667511590085 := by
  unfold tailWord_5046824
  simp only [CollatzResearch.WordTrace]
  refine ⟨92036396734113025881321763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122715195645484034508429017 92036396734113025881321763)
  ·
    refine ⟨138054595101169538821982645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92036396734113025881321763 138054595101169538821982645)
    ·
      refine ⟨12942618290734644264560873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138054595101169538821982645 12942618290734644264560873)
      ·
        refine ⟨9706963718050983198420655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12942618290734644264560873 9706963718050983198420655)
        ·
          refine ⟨14560445577076474797630983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9706963718050983198420655 14560445577076474797630983)
          ·
            refine ⟨21840668365614712196446475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14560445577076474797630983 21840668365614712196446475)
            ·
              refine ⟨32761002548422068294669713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21840668365614712196446475 32761002548422068294669713)
              ·
                refine ⟨24570751911316551221002285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32761002548422068294669713 24570751911316551221002285)
                ·
                  refine ⟨9214031966743706707875857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24570751911316551221002285 9214031966743706707875857)
                  ·
                    refine ⟨6910523975057780030906893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9214031966743706707875857 6910523975057780030906893)
                    ·
                      refine ⟨2591446490646667511590085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910523975057780030906893 2591446490646667511590085)
                      ·
                        rfl

theorem cell23_5046824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5046824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046824 prefixEnd_5046824 := by exact prefixLift 5046824
  have htrace : WordTrace (prefixWord ++ tailWord_5046824) baseStart_5046824 baseEnd_5046824 := by
    simpa [prefixWord, tailWord_5046824, baseEnd_5046824] using wordTrace_append hprefix tailTrace_5046824
  have hstable : (prefixWord ++ tailWord_5046824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046824).length < 2 ^ (prefixWord ++ tailWord_5046824).sum := by decide
  have hdescent : baseEnd_5046824 < baseStart_5046824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046838 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5046838 : Nat := 118140960795 + 5046838 * 2 ^ 59
def prefixEnd_5046838 : Nat := 4983230072969 + 3 ^ 40 * 5046838 * 2
def baseEnd_5046838 : Nat := 2591453679375830456815021

theorem tailTrace_5046838 : CollatzResearch.WordTrace tailWord_5046838 prefixEnd_5046838 2591453679375830456815021 := by
  unfold tailWord_5046838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504581505635958259603323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122715536060116888102435445 11504581505635958259603323)
  ·
    refine ⟨17256872258453937389404985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504581505635958259603323 17256872258453937389404985)
    ·
      refine ⟨12942654193840453042053739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17256872258453937389404985 12942654193840453042053739)
      ·
        refine ⟨19413981290760679563080609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12942654193840453042053739 19413981290760679563080609)
        ·
          refine ⟨14560485968070509672310457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19413981290760679563080609 14560485968070509672310457)
          ·
            refine ⟨10920364476052882254232843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14560485968070509672310457 10920364476052882254232843)
            ·
              refine ⟨16380546714079323381349265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10920364476052882254232843 16380546714079323381349265)
              ·
                refine ⟨12285410035559492536011949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16380546714079323381349265 12285410035559492536011949)
                ·
                  refine ⟨4607028763334809701004481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12285410035559492536011949 4607028763334809701004481)
                  ·
                    refine ⟨3455271572501107275753361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607028763334809701004481 3455271572501107275753361)
                    ·
                      refine ⟨2591453679375830456815021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455271572501107275753361 2591453679375830456815021)
                      ·
                        rfl

theorem cell23_5046838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5046838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046838 prefixEnd_5046838 := by exact prefixLift 5046838
  have htrace : WordTrace (prefixWord ++ tailWord_5046838) baseStart_5046838 baseEnd_5046838 := by
    simpa [prefixWord, tailWord_5046838, baseEnd_5046838] using wordTrace_append hprefix tailTrace_5046838
  have hstable : (prefixWord ++ tailWord_5046838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046838).length < 2 ^ (prefixWord ++ tailWord_5046838).sum := by decide
  have hdescent : baseEnd_5046838 < baseStart_5046838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046840 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_5046840 : Nat := 118140960795 + 5046840 * 2 ^ 59
def prefixEnd_5046840 : Nat := 4983230072969 + 3 ^ 40 * 5046840 * 2
def baseEnd_5046840 : Nat := 863818235445713149663337

theorem tailTrace_5046840 : CollatzResearch.WordTrace tailWord_5046840 prefixEnd_5046840 863818235445713149663337 := by
  unfold tailWord_5046840
  simp only [CollatzResearch.WordTrace]
  refine ⟨92036688518084043247612987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122715584690778724330150649 92036688518084043247612987)
  ·
    refine ⟨138055032777126064871419481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92036688518084043247612987 138055032777126064871419481)
    ·
      refine ⟨103541274582844548653564611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138055032777126064871419481 103541274582844548653564611)
      ·
        refine ⟨155311911874266822980346917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103541274582844548653564611 155311911874266822980346917)
        ·
          refine ⟨29120983476425029308815047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155311911874266822980346917 29120983476425029308815047)
          ·
            refine ⟨43681475214637543963222571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29120983476425029308815047 43681475214637543963222571)
            ·
              refine ⟨65522212821956315944833857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43681475214637543963222571 65522212821956315944833857)
              ·
                refine ⟨49141659616467236958625393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65522212821956315944833857 49141659616467236958625393)
                ·
                  refine ⟨36856244712350427718969045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49141659616467236958625393 36856244712350427718969045)
                  ·
                    refine ⟨863818235445713149663337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36856244712350427718969045 863818235445713149663337)
                    ·
                      rfl

theorem cell23_5046840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_5046840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046840 prefixEnd_5046840 := by exact prefixLift 5046840
  have htrace : WordTrace (prefixWord ++ tailWord_5046840) baseStart_5046840 baseEnd_5046840 := by
    simpa [prefixWord, tailWord_5046840, baseEnd_5046840] using wordTrace_append hprefix tailTrace_5046840
  have hstable : (prefixWord ++ tailWord_5046840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046840).length < 2 ^ (prefixWord ++ tailWord_5046840).sum := by decide
  have hdescent : baseEnd_5046840 < baseStart_5046840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046852 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5046852 : Nat := 118140960795 + 5046852 * 2 ^ 59
def prefixEnd_5046852 : Nat := 4983230072969 + 3 ^ 40 * 5046852 * 2
def baseEnd_5046852 : Nat := 863820289368331134013319

theorem tailTrace_5046852 : CollatzResearch.WordTrace tailWord_5046852 prefixEnd_5046852 863820289368331134013319 := by
  unfold tailWord_5046852
  simp only [CollatzResearch.WordTrace]
  refine ⟨92036907356062306272331405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122715876474749741696441873 92036907356062306272331405)
  ·
    refine ⟨34513840258523364852124277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92036907356062306272331405 34513840258523364852124277)
    ·
      refine ⟨3235672524236565454886651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34513840258523364852124277 3235672524236565454886651)
      ·
        refine ⟨4853508786354848182329977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3235672524236565454886651 4853508786354848182329977)
        ·
          refine ⟨3640131589766136136747483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853508786354848182329977 3640131589766136136747483)
          ·
            refine ⟨5460197384649204205121225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640131589766136136747483 5460197384649204205121225)
            ·
              refine ⟨4095148038486903153840919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5460197384649204205121225 4095148038486903153840919)
              ·
                refine ⟨6142722057730354730761379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095148038486903153840919 6142722057730354730761379)
                ·
                  refine ⟨9214083086595532096142069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6142722057730354730761379 9214083086595532096142069)
                  ·
                    refine ⟨863820289368331134013319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9214083086595532096142069 863820289368331134013319)
                    ·
                      rfl

theorem cell23_5046852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5046852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046852 prefixEnd_5046852 := by exact prefixLift 5046852
  have htrace : WordTrace (prefixWord ++ tailWord_5046852) baseStart_5046852 baseEnd_5046852 := by
    simpa [prefixWord, tailWord_5046852, baseEnd_5046852] using wordTrace_append hprefix tailTrace_5046852
  have hstable : (prefixWord ++ tailWord_5046852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046852).length < 2 ^ (prefixWord ++ tailWord_5046852).sum := by decide
  have hdescent : baseEnd_5046852 < baseStart_5046852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046888 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5046888 : Nat := 118140960795 + 5046888 * 2 ^ 59
def prefixEnd_5046888 : Nat := 4983230072969 + 3 ^ 40 * 5046888 * 2
def baseEnd_5046888 : Nat := 2591479353408555261189791

theorem tailTrace_5046888 : CollatzResearch.WordTrace tailWord_5046888 prefixEnd_5046888 2591479353408555261189791 := by
  unfold tailWord_5046888
  simp only [CollatzResearch.WordTrace]
  refine ⟨92037563869997095346486659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122716751826662793795315545 92037563869997095346486659)
  ·
    refine ⟨138056345804995643019729989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92037563869997095346486659 138056345804995643019729989)
    ·
      refine ⟨25885564838436683066199373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138056345804995643019729989 25885564838436683066199373)
      ·
        refine ⟨9707086814413756149824765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25885564838436683066199373 9707086814413756149824765)
        ·
          refine ⟨3640157555405158556184287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9707086814413756149824765 3640157555405158556184287)
          ·
            refine ⟨5460236333107737834276431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640157555405158556184287 5460236333107737834276431)
            ·
              refine ⟨8190354499661606751414647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460236333107737834276431 8190354499661606751414647)
              ·
                refine ⟨12285531749492410127121971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190354499661606751414647 12285531749492410127121971)
                ·
                  refine ⟨18428297624238615190682957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12285531749492410127121971 18428297624238615190682957)
                  ·
                    refine ⟨6910611609089480696506109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18428297624238615190682957 6910611609089480696506109)
                    ·
                      refine ⟨2591479353408555261189791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910611609089480696506109 2591479353408555261189791)
                      ·
                        rfl

theorem cell23_5046888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5046888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046888 prefixEnd_5046888 := by exact prefixLift 5046888
  have htrace : WordTrace (prefixWord ++ tailWord_5046888) baseStart_5046888 baseEnd_5046888 := by
    simpa [prefixWord, tailWord_5046888, baseEnd_5046888] using wordTrace_append hprefix tailTrace_5046888
  have hstable : (prefixWord ++ tailWord_5046888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046888).length < 2 ^ (prefixWord ++ tailWord_5046888).sum := by decide
  have hdescent : baseEnd_5046888 < baseStart_5046888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046898 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5046898 : Nat := 118140960795 + 5046898 * 2 ^ 59
def prefixEnd_5046898 : Nat := 4983230072969 + 3 ^ 40 * 5046898 * 2
def baseEnd_5046898 : Nat := 2591484488215100222064745

theorem tailTrace_5046898 : CollatzResearch.WordTrace tailWord_5046898 prefixEnd_5046898 2591484488215100222064745 := by
  unfold tailWord_5046898
  simp only [CollatzResearch.WordTrace]
  refine ⟨46018873117489490600209337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122716994979971974933891565 46018873117489490600209337)
  ·
    refine ⟨34514154838117117950157003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46018873117489490600209337 34514154838117117950157003)
    ·
      refine ⟨51771232257175676925235505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34514154838117117950157003 51771232257175676925235505)
      ·
        refine ⟨38828424192881757693926629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51771232257175676925235505 38828424192881757693926629)
        ·
          refine ⟨7280329536165329567611243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38828424192881757693926629 7280329536165329567611243)
          ·
            refine ⟨10920494304247994351416865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280329536165329567611243 10920494304247994351416865)
            ·
              refine ⟨8190370728185995763562649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10920494304247994351416865 8190370728185995763562649)
              ·
                refine ⟨6142778046139496822671987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8190370728185995763562649 6142778046139496822671987)
                ·
                  refine ⟨9214167069209245234007981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6142778046139496822671987 9214167069209245234007981)
                  ·
                    refine ⟨3455312650953466962752993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9214167069209245234007981 3455312650953466962752993)
                    ·
                      refine ⟨2591484488215100222064745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455312650953466962752993 2591484488215100222064745)
                      ·
                        rfl

theorem cell23_5046898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5046898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046898 prefixEnd_5046898 := by exact prefixLift 5046898
  have htrace : WordTrace (prefixWord ++ tailWord_5046898) baseStart_5046898 baseEnd_5046898 := by
    simpa [prefixWord, tailWord_5046898, baseEnd_5046898] using wordTrace_append hprefix tailTrace_5046898
  have hstable : (prefixWord ++ tailWord_5046898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046898).length < 2 ^ (prefixWord ++ tailWord_5046898).sum := by decide
  have hdescent : baseEnd_5046898 < baseStart_5046898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046984 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_5046984 : Nat := 118140960795 + 5046984 * 2 ^ 59
def prefixEnd_5046984 : Nat := 4983230072969 + 3 ^ 40 * 5046984 * 2
def baseEnd_5046984 : Nat := 2591528647551386885589349

theorem tailTrace_5046984 : CollatzResearch.WordTrace tailWord_5046984 prefixEnd_5046984 2591528647551386885589349 := by
  unfold tailWord_5046984
  simp only [CollatzResearch.WordTrace]
  refine ⟨92039314573823199544234003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122719086098430932725645337 92039314573823199544234003)
  ·
    refine ⟨138058971860734799316351005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92039314573823199544234003 138058971860734799316351005)
    ·
      refine ⟨51772114447775549743631627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138058971860734799316351005 51772114447775549743631627)
      ·
        refine ⟨77658171671663324615447441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51772114447775549743631627 77658171671663324615447441)
        ·
          refine ⟨58243628753747493461585581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77658171671663324615447441 58243628753747493461585581)
          ·
            refine ⟨21841360782655310048094593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58243628753747493461585581 21841360782655310048094593)
            ·
              refine ⟨16381020586991482536070945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21841360782655310048094593 16381020586991482536070945)
              ·
                refine ⟨12285765440243611902053209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16381020586991482536070945 12285765440243611902053209)
                ·
                  refine ⟨9214324080182708926539907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12285765440243611902053209 9214324080182708926539907)
                  ·
                    refine ⟨13821486120274063389809861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9214324080182708926539907 13821486120274063389809861)
                    ·
                      refine ⟨2591528647551386885589349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13821486120274063389809861 2591528647551386885589349)
                      ·
                        rfl

theorem cell23_5046984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_5046984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046984 prefixEnd_5046984 := by exact prefixLift 5046984
  have htrace : WordTrace (prefixWord ++ tailWord_5046984) baseStart_5046984 baseEnd_5046984 := by
    simpa [prefixWord, tailWord_5046984, baseEnd_5046984] using wordTrace_append hprefix tailTrace_5046984
  have hstable : (prefixWord ++ tailWord_5046984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046984).length < 2 ^ (prefixWord ++ tailWord_5046984).sum := by decide
  have hdescent : baseEnd_5046984 < baseStart_5046984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5046987 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3]
def baseStart_5046987 : Nat := 118140960795 + 5046987 * 2 ^ 59
def prefixEnd_5046987 : Nat := 4983230072969 + 3 ^ 40 * 5046987 * 2
def baseEnd_5046987 : Nat := 2591530187993350373851835

theorem tailTrace_5046987 : CollatzResearch.WordTrace tailWord_5046987 prefixEnd_5046987 2591530187993350373851835 := by
  unfold tailWord_5046987
  simp only [CollatzResearch.WordTrace]
  refine ⟨184078738566635530600827215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122719159044423687067218143 184078738566635530600827215)
  ·
    refine ⟨276118107849953295901240823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184078738566635530600827215 276118107849953295901240823)
    ·
      refine ⟨414177161774929943851861235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276118107849953295901240823 414177161774929943851861235)
      ·
        refine ⟨621265742662394915777791853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414177161774929943851861235 621265742662394915777791853)
        ·
          refine ⟨232974653498398093416671945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621265742662394915777791853 232974653498398093416671945)
          ·
            refine ⟨174730990123798570062503959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232974653498398093416671945 174730990123798570062503959)
            ·
              refine ⟨262096485185697855093755939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174730990123798570062503959 262096485185697855093755939)
              ·
                refine ⟨393144727778546782640633909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262096485185697855093755939 393144727778546782640633909)
                ·
                  refine ⟨36857318229238760872559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393144727778546782640633909 36857318229238760872559429)
                  ·
                    refine ⟨6910747167982267663604893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36857318229238760872559429 6910747167982267663604893)
                    ·
                      refine ⟨2591530187993350373851835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910747167982267663604893 2591530187993350373851835)
                      ·
                        rfl

theorem cell23_5046987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3].length) (baseStart_5046987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5046987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5046987 prefixEnd_5046987 := by exact prefixLift 5046987
  have htrace : WordTrace (prefixWord ++ tailWord_5046987) baseStart_5046987 baseEnd_5046987 := by
    simpa [prefixWord, tailWord_5046987, baseEnd_5046987] using wordTrace_append hprefix tailTrace_5046987
  have hstable : (prefixWord ++ tailWord_5046987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5046987).length < 2 ^ (prefixWord ++ tailWord_5046987).sum := by decide
  have hdescent : baseEnd_5046987 < baseStart_5046987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5046987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047011 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 3, 4]
def baseStart_5047011 : Nat := 118140960795 + 5047011 * 2 ^ 59
def prefixEnd_5047011 : Nat := 4983230072969 + 3 ^ 40 * 5047011 * 2
def baseEnd_5047011 : Nat := 863847503843019426650575

theorem tailTrace_5047011 : CollatzResearch.WordTrace tailWord_5047011 prefixEnd_5047011 863847503843019426650575 := by
  unfold tailWord_5047011
  simp only [CollatzResearch.WordTrace]
  refine ⟨184079613918548582699700887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122719742612365721799800591 184079613918548582699700887)
  ·
    refine ⟨276119420877822874049551331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184079613918548582699700887 276119420877822874049551331)
    ·
      refine ⟨414179131316734311074326997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276119420877822874049551331 414179131316734311074326997)
      ·
        refine ⟨9707323390235960415804539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 414179131316734311074326997 9707323390235960415804539)
        ·
          refine ⟨14560985085353940623706809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9707323390235960415804539 14560985085353940623706809)
          ·
            refine ⟨10920738814015455467780107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14560985085353940623706809 10920738814015455467780107)
            ·
              refine ⟨16381108221023183201670161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10920738814015455467780107 16381108221023183201670161)
              ·
                refine ⟨12285831165767387401252621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16381108221023183201670161 12285831165767387401252621)
                ·
                  refine ⟨4607186687162770275469733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12285831165767387401252621 4607186687162770275469733)
                  ·
                    refine ⟨863847503843019426650575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607186687162770275469733 863847503843019426650575)
                    ·
                      rfl

theorem cell23_5047011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 4].length) (baseStart_5047011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047011 prefixEnd_5047011 := by exact prefixLift 5047011
  have htrace : WordTrace (prefixWord ++ tailWord_5047011) baseStart_5047011 baseEnd_5047011 := by
    simpa [prefixWord, tailWord_5047011, baseEnd_5047011] using wordTrace_append hprefix tailTrace_5047011
  have hstable : (prefixWord ++ tailWord_5047011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047011).length < 2 ^ (prefixWord ++ tailWord_5047011).sum := by decide
  have hdescent : baseEnd_5047011 < baseStart_5047011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047071 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 1, 5]
def baseStart_5047071 : Nat := 118140960795 + 5047071 * 2 ^ 59
def prefixEnd_5047071 : Nat := 4983230072969 + 3 ^ 40 * 5047071 * 2
def baseEnd_5047071 : Nat := 863857773456109348400483

theorem tailTrace_5047071 : CollatzResearch.WordTrace tailWord_5047071 prefixEnd_5047071 863857773456109348400483 := by
  unfold tailWord_5047071
  simp only [CollatzResearch.WordTrace]
  refine ⟨184081802298331212946885067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122721201532220808631256711 184081802298331212946885067)
  ·
    refine ⟨276122703447496819420327601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184081802298331212946885067 276122703447496819420327601)
    ·
      refine ⟨207092027585622614565245701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276122703447496819420327601 207092027585622614565245701)
      ·
        refine ⟨38829755172304240230983569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207092027585622614565245701 38829755172304240230983569)
        ·
          refine ⟨29122316379228180173237677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38829755172304240230983569 29122316379228180173237677)
          ·
            refine ⟨10920868642210567564964129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29122316379228180173237677 10920868642210567564964129)
            ·
              refine ⟨8190651481657925673723097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10920868642210567564964129 8190651481657925673723097)
              ·
                refine ⟨6142988611243444255292323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8190651481657925673723097 6142988611243444255292323)
                ·
                  refine ⟨9214482916865166382938485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6142988611243444255292323 9214482916865166382938485)
                  ·
                    refine ⟨863857773456109348400483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9214482916865166382938485 863857773456109348400483)
                    ·
                      rfl

theorem cell23_5047071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_5047071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047071 prefixEnd_5047071 := by exact prefixLift 5047071
  have htrace : WordTrace (prefixWord ++ tailWord_5047071) baseStart_5047071 baseEnd_5047071 := by
    simpa [prefixWord, tailWord_5047071, baseEnd_5047071] using wordTrace_append hprefix tailTrace_5047071
  have hstable : (prefixWord ++ tailWord_5047071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047071).length < 2 ^ (prefixWord ++ tailWord_5047071).sum := by decide
  have hdescent : baseEnd_5047071 < baseStart_5047071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047084 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_5047084 : Nat := 118140960795 + 5047084 * 2 ^ 59
def prefixEnd_5047084 : Nat := 4983230072969 + 3 ^ 40 * 5047084 * 2
def baseEnd_5047084 : Nat := 863859998538945498112963

theorem tailTrace_5047084 : CollatzResearch.WordTrace tailWord_5047084 prefixEnd_5047084 863859998538945498112963 := by
  unfold tailWord_5047084
  simp only [CollatzResearch.WordTrace]
  refine ⟨92041138223642058083554153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122721517631522744111405537 92041138223642058083554153)
  ·
    refine ⟨69030853667731543562665615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92041138223642058083554153 69030853667731543562665615)
    ·
      refine ⟨103546280501597315343998423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69030853667731543562665615 103546280501597315343998423)
      ·
        refine ⟨155319420752395973015997635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103546280501597315343998423 155319420752395973015997635)
        ·
          refine ⟨232979131128593959523996453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155319420752395973015997635 232979131128593959523996453)
          ·
            refine ⟨43683587086611367410749335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232979131128593959523996453 43683587086611367410749335)
            ·
              refine ⟨65525380629917051116124003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43683587086611367410749335 65525380629917051116124003)
              ·
                refine ⟨98288070944875576674186005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65525380629917051116124003 98288070944875576674186005)
                ·
                  refine ⟨4607253325541042656602469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98288070944875576674186005 4607253325541042656602469)
                  ·
                    refine ⟨863859998538945498112963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607253325541042656602469 863859998538945498112963)
                    ·
                      rfl

theorem cell23_5047084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_5047084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047084 prefixEnd_5047084 := by exact prefixLift 5047084
  have htrace : WordTrace (prefixWord ++ tailWord_5047084) baseStart_5047084 baseEnd_5047084 := by
    simpa [prefixWord, tailWord_5047084, baseEnd_5047084] using wordTrace_append hprefix tailTrace_5047084
  have hstable : (prefixWord ++ tailWord_5047084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047084).length < 2 ^ (prefixWord ++ tailWord_5047084).sum := by decide
  have hdescent : baseEnd_5047084 < baseStart_5047084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047087 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_5047087 : Nat := 118140960795 + 5047087 * 2 ^ 59
def prefixEnd_5047087 : Nat := 4983230072969 + 3 ^ 40 * 5047087 * 2
def baseEnd_5047087 : Nat := 2591581536058799982601375

theorem tailTrace_5047087 : CollatzResearch.WordTrace tailWord_5047087 prefixEnd_5047087 2591581536058799982601375 := by
  unfold tailWord_5047087
  simp only [CollatzResearch.WordTrace]
  refine ⟨184082385866273247679467515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122721590577515498452978343 184082385866273247679467515)
  ·
    refine ⟨276123578799409871519201273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184082385866273247679467515 276123578799409871519201273)
    ·
      refine ⟨207092684099557403639400955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276123578799409871519201273 207092684099557403639400955)
      ·
        refine ⟨310639026149336105459101433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207092684099557403639400955 310639026149336105459101433)
        ·
          refine ⟨232979269612002079094326075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310639026149336105459101433 232979269612002079094326075)
          ·
            refine ⟨349468904418003118641489113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232979269612002079094326075 349468904418003118641489113)
            ·
              refine ⟨262101678313502338981116835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349468904418003118641489113 262101678313502338981116835)
              ·
                refine ⟨393152517470253508471675253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262101678313502338981116835 393152517470253508471675253)
                ·
                  refine ⟨36858048512836266419219555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393152517470253508471675253 36858048512836266419219555)
                  ·
                    refine ⟨55287072769254399628829333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36858048512836266419219555 55287072769254399628829333)
                    ·
                      refine ⟨2591581536058799982601375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55287072769254399628829333 2591581536058799982601375)
                      ·
                        rfl

theorem cell23_5047087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_5047087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047087 prefixEnd_5047087 := by exact prefixLift 5047087
  have htrace : WordTrace (prefixWord ++ tailWord_5047087) baseStart_5047087 baseEnd_5047087 := by
    simpa [prefixWord, tailWord_5047087, baseEnd_5047087] using wordTrace_append hprefix tailTrace_5047087
  have hstable : (prefixWord ++ tailWord_5047087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047087).length < 2 ^ (prefixWord ++ tailWord_5047087).sum := by decide
  have hdescent : baseEnd_5047087 < baseStart_5047087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047091 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 4]
def baseStart_5047091 : Nat := 118140960795 + 5047091 * 2 ^ 59
def prefixEnd_5047091 : Nat := 4983230072969 + 3 ^ 40 * 5047091 * 2
def baseEnd_5047091 : Nat := 2591583589981417966951357

theorem tailTrace_5047091 : CollatzResearch.WordTrace tailWord_5047091 prefixEnd_5047091 2591583589981417966951357 := by
  unfold tailWord_5047091
  simp only [CollatzResearch.WordTrace]
  refine ⟨184082531758258756362613127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122721687838839170908408751 184082531758258756362613127)
  ·
    refine ⟨276123797637388134543919691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184082531758258756362613127 276123797637388134543919691)
    ·
      refine ⟨414185696456082201815879537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276123797637388134543919691 414185696456082201815879537)
      ·
        refine ⟨310639272342061651361909653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414185696456082201815879537 310639272342061651361909653)
        ·
          refine ⟨14561215891034139907589515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 310639272342061651361909653 14561215891034139907589515)
          ·
            refine ⟨21841823836551209861384273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14561215891034139907589515 21841823836551209861384273)
            ·
              refine ⟨16381367877413407396038205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21841823836551209861384273 16381367877413407396038205)
              ·
                refine ⟨6143012954030027773514327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16381367877413407396038205 6143012954030027773514327)
                ·
                  refine ⟨9214519431045041660271491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143012954030027773514327 9214519431045041660271491)
                  ·
                    refine ⟨13821779146567562490407237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9214519431045041660271491 13821779146567562490407237)
                    ·
                      refine ⟨2591583589981417966951357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13821779146567562490407237 2591583589981417966951357)
                      ·
                        rfl

theorem cell23_5047091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_5047091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047091 prefixEnd_5047091 := by exact prefixLift 5047091
  have htrace : WordTrace (prefixWord ++ tailWord_5047091) baseStart_5047091 baseEnd_5047091 := by
    simpa [prefixWord, tailWord_5047091, baseEnd_5047091] using wordTrace_append hprefix tailTrace_5047091
  have hstable : (prefixWord ++ tailWord_5047091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047091).length < 2 ^ (prefixWord ++ tailWord_5047091).sum := by decide
  have hdescent : baseEnd_5047091 < baseStart_5047091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047102 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_5047102 : Nat := 118140960795 + 5047102 * 2 ^ 59
def prefixEnd_5047102 : Nat := 4983230072969 + 3 ^ 40 * 5047102 * 2
def baseEnd_5047102 : Nat := 2591589238268617423913807

theorem tailTrace_5047102 : CollatzResearch.WordTrace tailWord_5047102 prefixEnd_5047102 2591589238268617423913807 := by
  unfold tailWord_5047102
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010366620152363155157945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122721955307479270160842373 23010366620152363155157945)
  ·
    refine ⟨17257774965114272366368459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23010366620152363155157945 17257774965114272366368459)
    ·
      refine ⟨25886662447671408549552689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17257774965114272366368459 25886662447671408549552689)
      ·
        refine ⟨19414996835753556412164517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25886662447671408549552689 19414996835753556412164517)
        ·
          refine ⟨3640311906703791827280847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19414996835753556412164517 3640311906703791827280847)
          ·
            refine ⟨5460467860055687740921271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640311906703791827280847 5460467860055687740921271)
            ·
              refine ⟨8190701790083531611381907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460467860055687740921271 8190701790083531611381907)
              ·
                refine ⟨12286052685125297417072861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190701790083531611381907 12286052685125297417072861)
                ·
                  refine ⟨4607269756921986531402323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12286052685125297417072861 4607269756921986531402323)
                  ·
                    refine ⟨6910904635382979797103485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607269756921986531402323 6910904635382979797103485)
                    ·
                      refine ⟨2591589238268617423913807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910904635382979797103485 2591589238268617423913807)
                      ·
                        rfl

theorem cell23_5047102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_5047102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047102 prefixEnd_5047102 := by exact prefixLift 5047102
  have htrace : WordTrace (prefixWord ++ tailWord_5047102) baseStart_5047102 baseEnd_5047102 := by
    simpa [prefixWord, tailWord_5047102, baseEnd_5047102] using wordTrace_append hprefix tailTrace_5047102
  have hstable : (prefixWord ++ tailWord_5047102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047102).length < 2 ^ (prefixWord ++ tailWord_5047102).sum := by decide
  have hdescent : baseEnd_5047102 < baseStart_5047102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047138 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5047138 : Nat := 118140960795 + 5047138 * 2 ^ 59
def prefixEnd_5047138 : Nat := 4983230072969 + 3 ^ 40 * 5047138 * 2
def baseEnd_5047138 : Nat := 2591607723572179283063641

theorem tailTrace_5047138 : CollatzResearch.WordTrace tailWord_5047138 prefixEnd_5047138 2591607723572179283063641 := by
  unfold tailWord_5047138
  simp only [CollatzResearch.WordTrace]
  refine ⟨46021061497272120847393517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122722830659392322259716045 46021061497272120847393517)
  ·
    refine ⟨17257898061477045317772569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46021061497272120847393517 17257898061477045317772569)
    ·
      refine ⟨12943423546107783988329427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17257898061477045317772569 12943423546107783988329427)
      ·
        refine ⟨19415135319161675982494141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12943423546107783988329427 19415135319161675982494141)
        ·
          refine ⟨7280675744685628493435303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19415135319161675982494141 7280675744685628493435303)
          ·
            refine ⟨10921013617028442740152955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280675744685628493435303 10921013617028442740152955)
            ·
              refine ⟨16381520425542664110229433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10921013617028442740152955 16381520425542664110229433)
              ·
                refine ⟨12286140319156998082672075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16381520425542664110229433 12286140319156998082672075)
                ·
                  refine ⟨18429210478735497124008113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12286140319156998082672075 18429210478735497124008113)
                  ·
                    refine ⟨13821907859051622843006085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18429210478735497124008113 13821907859051622843006085)
                    ·
                      refine ⟨2591607723572179283063641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13821907859051622843006085 2591607723572179283063641)
                      ·
                        rfl

theorem cell23_5047138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5047138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047138 prefixEnd_5047138 := by exact prefixLift 5047138
  have htrace : WordTrace (prefixWord ++ tailWord_5047138) baseStart_5047138 baseEnd_5047138 := by
    simpa [prefixWord, tailWord_5047138, baseEnd_5047138] using wordTrace_append hprefix tailTrace_5047138
  have hstable : (prefixWord ++ tailWord_5047138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047138).length < 2 ^ (prefixWord ++ tailWord_5047138).sum := by decide
  have hdescent : baseEnd_5047138 < baseStart_5047138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047141 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_5047141 : Nat := 118140960795 + 5047141 * 2 ^ 59
def prefixEnd_5047141 : Nat := 4983230072969 + 3 ^ 40 * 5047141 * 2
def baseEnd_5047141 : Nat := 2591609264014142771326127

theorem tailTrace_5047141 : CollatzResearch.WordTrace tailWord_5047141 prefixEnd_5047141 2591609264014142771326127 := by
  unfold tailWord_5047141
  simp only [CollatzResearch.WordTrace]
  refine ⟨184084355408077614901933277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122722903605385076601288851 184084355408077614901933277)
  ·
    refine ⟨69031633278029105588224979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184084355408077614901933277 69031633278029105588224979)
    ·
      refine ⟨103547449917043658382337469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69031633278029105588224979 103547449917043658382337469)
      ·
        refine ⟨38830293718891371893376551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103547449917043658382337469 38830293718891371893376551)
        ·
          refine ⟨58245440578337057840064827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38830293718891371893376551 58245440578337057840064827)
          ·
            refine ⟨87368160867505586760097241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58245440578337057840064827 87368160867505586760097241)
            ·
              refine ⟨65526120650629190070072931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87368160867505586760097241 65526120650629190070072931)
              ·
                refine ⟨98289180975943785105109397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65526120650629190070072931 98289180975943785105109397)
                ·
                  refine ⟨4607305358247364926802003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98289180975943785105109397 4607305358247364926802003)
                  ·
                    refine ⟨6910958037371047390203005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607305358247364926802003 6910958037371047390203005)
                    ·
                      refine ⟨2591609264014142771326127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6910958037371047390203005 2591609264014142771326127)
                      ·
                        rfl

theorem cell23_5047141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_5047141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047141 prefixEnd_5047141 := by exact prefixLift 5047141
  have htrace : WordTrace (prefixWord ++ tailWord_5047141) baseStart_5047141 baseEnd_5047141 := by
    simpa [prefixWord, tailWord_5047141, baseEnd_5047141] using wordTrace_append hprefix tailTrace_5047141
  have hstable : (prefixWord ++ tailWord_5047141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047141).length < 2 ^ (prefixWord ++ tailWord_5047141).sum := by decide
  have hdescent : baseEnd_5047141 < baseStart_5047141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047154 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5047154 : Nat := 118140960795 + 5047154 * 2 ^ 59
def prefixEnd_5047154 : Nat := 4983230072969 + 3 ^ 40 * 5047154 * 2
def baseEnd_5047154 : Nat := 2591615939262651220463567

theorem tailTrace_5047154 : CollatzResearch.WordTrace tailWord_5047154 prefixEnd_5047154 2591615939262651220463567 := by
  unfold tailWord_5047154
  simp only [CollatzResearch.WordTrace]
  refine ⟨46021207389257629530539129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122723219704687012081437677 46021207389257629530539129)
  ·
    refine ⟨34515905541943222147904347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46021207389257629530539129 34515905541943222147904347)
    ·
      refine ⟨51773858312914833221856521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34515905541943222147904347 51773858312914833221856521)
      ·
        refine ⟨38830393734686124916392391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51773858312914833221856521 38830393734686124916392391)
        ·
          refine ⟨58245590602029187374588587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38830393734686124916392391 58245590602029187374588587)
          ·
            refine ⟨87368385903043781061882881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58245590602029187374588587 87368385903043781061882881)
            ·
              refine ⟨65526289427282835796412161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87368385903043781061882881 65526289427282835796412161)
              ·
                refine ⟨49144717070462126847309121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65526289427282835796412161 49144717070462126847309121)
                ·
                  refine ⟨36858537802846595135481841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49144717070462126847309121 36858537802846595135481841)
                  ·
                    refine ⟨27643903352134946351611381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36858537802846595135481841 27643903352134946351611381)
                    ·
                      refine ⟨2591615939262651220463567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27643903352134946351611381 2591615939262651220463567)
                      ·
                        rfl

theorem cell23_5047154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5047154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047154 prefixEnd_5047154 := by exact prefixLift 5047154
  have htrace : WordTrace (prefixWord ++ tailWord_5047154) baseStart_5047154 baseEnd_5047154 := by
    simpa [prefixWord, tailWord_5047154, baseEnd_5047154] using wordTrace_append hprefix tailTrace_5047154
  have hstable : (prefixWord ++ tailWord_5047154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047154).length < 2 ^ (prefixWord ++ tailWord_5047154).sum := by decide
  have hdescent : baseEnd_5047154 < baseStart_5047154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047184 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_5047184 : Nat := 118140960795 + 5047184 * 2 ^ 59
def prefixEnd_5047184 : Nat := 4983230072969 + 3 ^ 40 * 5047184 * 2
def baseEnd_5047184 : Nat := 2591631343682286103088429

theorem tailTrace_5047184 : CollatzResearch.WordTrace tailWord_5047184 prefixEnd_5047184 2591631343682286103088429 := by
  unfold tailWord_5047184
  simp only [CollatzResearch.WordTrace]
  refine ⟨92042961873460916622874303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122723949164614555497165737 92042961873460916622874303)
  ·
    refine ⟨138064442810191374934311455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92042961873460916622874303 138064442810191374934311455)
    ·
      refine ⟨207096664215287062401467183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138064442810191374934311455 207096664215287062401467183)
      ·
        refine ⟨310644996322930593602200775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207096664215287062401467183 310644996322930593602200775)
        ·
          refine ⟨465967494484395890403301163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310644996322930593602200775 465967494484395890403301163)
          ·
            refine ⟨698951241726593835604951745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465967494484395890403301163 698951241726593835604951745)
            ·
              refine ⟨524213431294945376703713809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698951241726593835604951745 524213431294945376703713809)
              ·
                refine ⟨393160073471209032527785357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524213431294945376703713809 393160073471209032527785357)
                ·
                  refine ⟨147435027551703387197919509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393160073471209032527785357 147435027551703387197919509)
                  ·
                    refine ⟨6911016916486096274902477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 147435027551703387197919509 6911016916486096274902477)
                    ·
                      refine ⟨2591631343682286103088429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911016916486096274902477 2591631343682286103088429)
                      ·
                        rfl

theorem cell23_5047184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_5047184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047184 prefixEnd_5047184 := by exact prefixLift 5047184
  have htrace : WordTrace (prefixWord ++ tailWord_5047184) baseStart_5047184 baseEnd_5047184 := by
    simpa [prefixWord, tailWord_5047184, baseEnd_5047184] using wordTrace_append hprefix tailTrace_5047184
  have hstable : (prefixWord ++ tailWord_5047184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047184).length < 2 ^ (prefixWord ++ tailWord_5047184).sum := by decide
  have hdescent : baseEnd_5047184 < baseStart_5047184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047202 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_5047202 : Nat := 118140960795 + 5047202 * 2 ^ 59
def prefixEnd_5047202 : Nat := 4983230072969 + 3 ^ 40 * 5047202 * 2
def baseEnd_5047202 : Nat := 2591640586334067032663347

theorem tailTrace_5047202 : CollatzResearch.WordTrace tailWord_5047202 prefixEnd_5047202 2591640586334067032663347 := by
  unfold tailWord_5047202
  simp only [CollatzResearch.WordTrace]
  refine ⟨46021645065214155579975965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122724386840571081546602573 46021645065214155579975965)
  ·
    refine ⟨17258116899455308342490987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46021645065214155579975965 17258116899455308342490987)
    ·
      refine ⟨25887175349182962513736481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17258116899455308342490987 25887175349182962513736481)
      ·
        refine ⟨19415381511887221885302361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25887175349182962513736481 19415381511887221885302361)
        ·
          refine ⟨14561536133915416413976771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19415381511887221885302361 14561536133915416413976771)
          ·
            refine ⟨21842304200873124620965157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14561536133915416413976771 21842304200873124620965157)
            ·
              refine ⟨4095432037663710866430967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21842304200873124620965157 4095432037663710866430967)
              ·
                refine ⟨6143148056495566299646451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095432037663710866430967 6143148056495566299646451)
                ·
                  refine ⟨9214722084743349449469677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143148056495566299646451 9214722084743349449469677)
                  ·
                    refine ⟨3455520781778756043551129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9214722084743349449469677 3455520781778756043551129)
                    ·
                      refine ⟨2591640586334067032663347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455520781778756043551129 2591640586334067032663347)
                      ·
                        rfl

theorem cell23_5047202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_5047202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047202 prefixEnd_5047202 := by exact prefixLift 5047202
  have htrace : WordTrace (prefixWord ++ tailWord_5047202) baseStart_5047202 baseEnd_5047202 := by
    simpa [prefixWord, tailWord_5047202, baseEnd_5047202] using wordTrace_append hprefix tailTrace_5047202
  have hstable : (prefixWord ++ tailWord_5047202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047202).length < 2 ^ (prefixWord ++ tailWord_5047202).sum := by decide
  have hdescent : baseEnd_5047202 < baseStart_5047202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047204 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 9]
def baseStart_5047204 : Nat := 118140960795 + 5047204 * 2 ^ 59
def prefixEnd_5047204 : Nat := 4983230072969 + 3 ^ 40 * 5047204 * 2
def baseEnd_5047204 : Nat := 287960179255041780537593

theorem tailTrace_5047204 : CollatzResearch.WordTrace tailWord_5047204 prefixEnd_5047204 287960179255041780537593 := by
  unfold tailWord_5047204
  simp only [CollatzResearch.WordTrace]
  refine ⟨92043326603424688330738333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122724435471232917774317777 92043326603424688330738333)
  ·
    refine ⟨34516247476284258124026875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92043326603424688330738333 34516247476284258124026875)
    ·
      refine ⟨51774371214426387186040313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34516247476284258124026875 51774371214426387186040313)
      ·
        refine ⟨38830778410819790389530235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51774371214426387186040313 38830778410819790389530235)
        ·
          refine ⟨58246167616229685584295353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38830778410819790389530235 58246167616229685584295353)
          ·
            refine ⟨43684625712172264188221515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58246167616229685584295353 43684625712172264188221515)
            ·
              refine ⟨65526938568258396282332273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43684625712172264188221515 65526938568258396282332273)
              ·
                refine ⟨49145203926193797211749205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65526938568258396282332273 49145203926193797211749205)
                ·
                  refine ⟨287960179255041780537593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49145203926193797211749205 287960179255041780537593)
                  ·
                    rfl

theorem cell23_5047204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_5047204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047204 prefixEnd_5047204 := by exact prefixLift 5047204
  have htrace : WordTrace (prefixWord ++ tailWord_5047204) baseStart_5047204 baseEnd_5047204 := by
    simpa [prefixWord, tailWord_5047204, baseEnd_5047204] using wordTrace_append hprefix tailTrace_5047204
  have hstable : (prefixWord ++ tailWord_5047204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047204).length < 2 ^ (prefixWord ++ tailWord_5047204).sum := by decide
  have hdescent : baseEnd_5047204 < baseStart_5047204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047221 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 7]
def baseStart_5047221 : Nat := 118140960795 + 5047221 * 2 ^ 59
def prefixEnd_5047221 : Nat := 4983230072969 + 3 ^ 40 * 5047221 * 2
def baseEnd_5047221 : Nat := 287961149162944717591751

theorem tailTrace_5047221 : CollatzResearch.WordTrace tailWord_5047221 prefixEnd_5047221 287961149162944717591751 := by
  unfold tailWord_5047221
  simp only [CollatzResearch.WordTrace]
  refine ⟨184087273247787788564845517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122724848831858525709897011 184087273247787788564845517)
  ·
    refine ⟨69032727467920420711817069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184087273247787788564845517 69032727467920420711817069)
    ·
      refine ⟨25887272800470157766931401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69032727467920420711817069 25887272800470157766931401)
      ·
        refine ⟨19415454600352618325198551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25887272800470157766931401 19415454600352618325198551)
        ·
          refine ⟨29123181900528927487797827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19415454600352618325198551 29123181900528927487797827)
          ·
            refine ⟨43684772850793391231696741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29123181900528927487797827 43684772850793391231696741)
            ·
              refine ⟨8190894909523760855943139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43684772850793391231696741 8190894909523760855943139)
              ·
                refine ⟨12286342364285641283914709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8190894909523760855943139 12286342364285641283914709)
                ·
                  refine ⟨287961149162944717591751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12286342364285641283914709 287961149162944717591751)
                  ·
                    rfl

theorem cell23_5047221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_5047221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047221 prefixEnd_5047221 := by exact prefixLift 5047221
  have htrace : WordTrace (prefixWord ++ tailWord_5047221) baseStart_5047221 baseEnd_5047221 := by
    simpa [prefixWord, tailWord_5047221, baseEnd_5047221] using wordTrace_append hprefix tailTrace_5047221
  have hstable : (prefixWord ++ tailWord_5047221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047221).length < 2 ^ (prefixWord ++ tailWord_5047221).sum := by decide
  have hdescent : baseEnd_5047221 < baseStart_5047221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047232 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2]
def baseStart_5047232 : Nat := 118140960795 + 5047232 * 2 ^ 59
def prefixEnd_5047232 : Nat := 4983230072969 + 3 ^ 40 * 5047232 * 2
def baseEnd_5047232 : Nat := 2591655990753701915288209

theorem tailTrace_5047232 : CollatzResearch.WordTrace tailWord_5047232 prefixEnd_5047232 2591655990753701915288209 := by
  unfold tailWord_5047232
  simp only [CollatzResearch.WordTrace]
  refine ⟨92043837225373968721747975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122725116300498624962330633 92043837225373968721747975)
  ·
    refine ⟨138065755838060953082621963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92043837225373968721747975 138065755838060953082621963)
    ·
      refine ⟨207098633757091429623932945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138065755838060953082621963 207098633757091429623932945)
      ·
        refine ⟨155323975317818572217949709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207098633757091429623932945 155323975317818572217949709)
        ·
          refine ⟨58246490744181964581731141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155323975317818572217949709 58246490744181964581731141)
          ·
            refine ⟨10921217014534118359074589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58246490744181964581731141 10921217014534118359074589)
            ·
              refine ⟨4095456380450294384652971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10921217014534118359074589 4095456380450294384652971)
              ·
                refine ⟨6143184570675441576979457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095456380450294384652971 6143184570675441576979457)
                ·
                  refine ⟨4607388428006581182734593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6143184570675441576979457 4607388428006581182734593)
                  ·
                    refine ⟨3455541321004935887050945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607388428006581182734593 3455541321004935887050945)
                    ·
                      refine ⟨2591655990753701915288209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455541321004935887050945 2591655990753701915288209)
                      ·
                        rfl

theorem cell23_5047232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_5047232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047232 prefixEnd_5047232 := by exact prefixLift 5047232
  have htrace : WordTrace (prefixWord ++ tailWord_5047232) baseStart_5047232 baseEnd_5047232 := by
    simpa [prefixWord, tailWord_5047232, baseEnd_5047232] using wordTrace_append hprefix tailTrace_5047232
  have hstable : (prefixWord ++ tailWord_5047232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047232).length < 2 ^ (prefixWord ++ tailWord_5047232).sum := by decide
  have hdescent : baseEnd_5047232 < baseStart_5047232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047278 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_5047278 : Nat := 118140960795 + 5047278 * 2 ^ 59
def prefixEnd_5047278 : Nat := 4983230072969 + 3 ^ 40 * 5047278 * 2
def baseEnd_5047278 : Nat := 2591679610863808735312997

theorem tailTrace_5047278 : CollatzResearch.WordTrace tailWord_5047278 prefixEnd_5047278 2591679610863808735312997 := by
  unfold tailWord_5047278
  simp only [CollatzResearch.WordTrace]
  refine ⟨23011169026072660912458811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122726234805720858199780325 23011169026072660912458811)
  ·
    refine ⟨34516753539108991368688217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23011169026072660912458811 34516753539108991368688217)
    ·
      refine ⟨25887565154331743526516163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34516753539108991368688217 25887565154331743526516163)
      ·
        refine ⟨38831347731497615289774245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25887565154331743526516163 38831347731497615289774245)
        ·
          refine ⟨7280877699655802866832671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38831347731497615289774245 7280877699655802866832671)
          ·
            refine ⟨10921316549483704300249007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7280877699655802866832671 10921316549483704300249007)
            ·
              refine ⟨16381974824225556450373511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10921316549483704300249007 16381974824225556450373511)
              ·
                refine ⟨24572962236338334675560267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16381974824225556450373511 24572962236338334675560267)
                ·
                  refine ⟨36859443354507502013340401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24572962236338334675560267 36859443354507502013340401)
                  ·
                    refine ⟨27644582515880626510005301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36859443354507502013340401 27644582515880626510005301)
                    ·
                      refine ⟨2591679610863808735312997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27644582515880626510005301 2591679610863808735312997)
                      ·
                        rfl

theorem cell23_5047278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_5047278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047278 prefixEnd_5047278 := by exact prefixLift 5047278
  have htrace : WordTrace (prefixWord ++ tailWord_5047278) baseStart_5047278 baseEnd_5047278 := by
    simpa [prefixWord, tailWord_5047278, baseEnd_5047278] using wordTrace_append hprefix tailTrace_5047278
  have hstable : (prefixWord ++ tailWord_5047278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047278).length < 2 ^ (prefixWord ++ tailWord_5047278).sum := by decide
  have hdescent : baseEnd_5047278 < baseStart_5047278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047291 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3]
def baseStart_5047291 : Nat := 118140960795 + 5047291 * 2 ^ 59
def prefixEnd_5047291 : Nat := 4983230072969 + 3 ^ 40 * 5047291 * 2
def baseEnd_5047291 : Nat := 2591686286112317184450437

theorem tailTrace_5047291 : CollatzResearch.WordTrace tailWord_5047291 prefixEnd_5047291 2591686286112317184450437 := by
  unfold tailWord_5047291
  simp only [CollatzResearch.WordTrace]
  refine ⟨184089826357534190519893727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122726550905022793679929151 184089826357534190519893727)
  ·
    refine ⟨276134739536301285779840591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184089826357534190519893727 276134739536301285779840591)
    ·
      refine ⟨414202109304451928669760887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276134739536301285779840591 414202109304451928669760887)
      ·
        refine ⟨621303163956677893004641331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414202109304451928669760887 621303163956677893004641331)
        ·
          refine ⟨931954745935016839506961997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621303163956677893004641331 931954745935016839506961997)
          ·
            refine ⟨349483029725631314815110749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 931954745935016839506961997 349483029725631314815110749)
            ·
              refine ⟨131056136147111743055666531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349483029725631314815110749 131056136147111743055666531)
              ·
                refine ⟨196584204220667614583499797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131056136147111743055666531 196584204220667614583499797)
                ·
                  refine ⟨9214884572843794433601553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196584204220667614583499797 9214884572843794433601553)
                  ·
                    refine ⟨6911163429632845825201165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9214884572843794433601553 6911163429632845825201165)
                    ·
                      refine ⟨2591686286112317184450437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911163429632845825201165 2591686286112317184450437)
                      ·
                        rfl

theorem cell23_5047291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3].length) (baseStart_5047291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047291 prefixEnd_5047291 := by exact prefixLift 5047291
  have htrace : WordTrace (prefixWord ++ tailWord_5047291) baseStart_5047291 baseEnd_5047291 := by
    simpa [prefixWord, tailWord_5047291, baseEnd_5047291] using wordTrace_append hprefix tailTrace_5047291
  have hstable : (prefixWord ++ tailWord_5047291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047291).length < 2 ^ (prefixWord ++ tailWord_5047291).sum := by decide
  have hdescent : baseEnd_5047291 < baseStart_5047291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047308 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_5047308 : Nat := 118140960795 + 5047308 * 2 ^ 59
def prefixEnd_5047308 : Nat := 4983230072969 + 3 ^ 40 * 5047308 * 2
def baseEnd_5047308 : Nat := 2591695015283443617937859

theorem tailTrace_5047308 : CollatzResearch.WordTrace tailWord_5047308 prefixEnd_5047308 2591695015283443617937859 := by
  unfold tailWord_5047308
  simp only [CollatzResearch.WordTrace]
  refine ⟨92045223199236301211631289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122726964265648401615508385 92045223199236301211631289)
  ·
    refine ⟨69033917399427225908723467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92045223199236301211631289 69033917399427225908723467)
    ·
      refine ⟨103550876099140838863085201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69033917399427225908723467 103550876099140838863085201)
      ·
        refine ⟨77663157074355629147313901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103550876099140838863085201 77663157074355629147313901)
        ·
          refine ⟨29123683902883360930242713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77663157074355629147313901 29123683902883360930242713)
          ·
            refine ⟨21842762927162520697682035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29123683902883360930242713 21842762927162520697682035)
            ·
              refine ⟨32764144390743781046523053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21842762927162520697682035 32764144390743781046523053)
              ·
                refine ⟨12286554146528917892446145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32764144390743781046523053 12286554146528917892446145)
                ·
                  refine ⟨9214915609896688419334609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12286554146528917892446145 9214915609896688419334609)
                  ·
                    refine ⟨6911186707422516314500957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9214915609896688419334609 6911186707422516314500957)
                    ·
                      refine ⟨2591695015283443617937859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911186707422516314500957 2591695015283443617937859)
                      ·
                        rfl

theorem cell23_5047308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_5047308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047308 prefixEnd_5047308 := by exact prefixLift 5047308
  have htrace : WordTrace (prefixWord ++ tailWord_5047308) baseStart_5047308 baseEnd_5047308 := by
    simpa [prefixWord, tailWord_5047308, baseEnd_5047308] using wordTrace_append hprefix tailTrace_5047308
  have hstable : (prefixWord ++ tailWord_5047308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047308).length < 2 ^ (prefixWord ++ tailWord_5047308).sum := by decide
  have hdescent : baseEnd_5047308 < baseStart_5047308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047332 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_5047332 : Nat := 118140960795 + 5047332 * 2 ^ 59
def prefixEnd_5047332 : Nat := 4983230072969 + 3 ^ 40 * 5047332 * 2
def baseEnd_5047332 : Nat := 863902446273050508012583

theorem tailTrace_5047332 : CollatzResearch.WordTrace tailWord_5047332 prefixEnd_5047332 863902446273050508012583 := by
  unfold tailWord_5047332
  simp only [CollatzResearch.WordTrace]
  refine ⟨92045660875192827261068125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122727547833590436348090833 92045660875192827261068125)
  ·
    refine ⟨34517122828197310222900547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92045660875192827261068125 34517122828197310222900547)
    ·
      refine ⟨51775684242295965334350821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34517122828197310222900547 51775684242295965334350821)
      ·
        refine ⟨9707940795430493500190779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51775684242295965334350821 9707940795430493500190779)
        ·
          refine ⟨14561911193145740250286169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9707940795430493500190779 14561911193145740250286169)
          ·
            refine ⟨10921433394859305187714627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14561911193145740250286169 10921433394859305187714627)
            ·
              refine ⟨16382150092288957781571941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10921433394859305187714627 16382150092288957781571941)
              ·
                refine ⟨3071653142304179584044739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16382150092288957781571941 3071653142304179584044739)
                ·
                  refine ⟨4607479713456269376067109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071653142304179584044739 4607479713456269376067109)
                  ·
                    refine ⟨863902446273050508012583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607479713456269376067109 863902446273050508012583)
                    ·
                      rfl

theorem cell23_5047332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_5047332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047332 prefixEnd_5047332 := by exact prefixLift 5047332
  have htrace : WordTrace (prefixWord ++ tailWord_5047332) baseStart_5047332 baseEnd_5047332 := by
    simpa [prefixWord, tailWord_5047332, baseEnd_5047332] using wordTrace_append hprefix tailTrace_5047332
  have hstable : (prefixWord ++ tailWord_5047332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047332).length < 2 ^ (prefixWord ++ tailWord_5047332).sum := by decide
  have hdescent : baseEnd_5047332 < baseStart_5047332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047365 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 2, 3, 2]
def baseStart_5047365 : Nat := 118140960795 + 5047365 * 2 ^ 59
def prefixEnd_5047365 : Nat := 4983230072969 + 3 ^ 40 * 5047365 * 2
def baseEnd_5047365 : Nat := 2591724283680749894925097

theorem tailTrace_5047365 : CollatzResearch.WordTrace tailWord_5047365 prefixEnd_5047365 2591724283680749894925097 := by
  unfold tailWord_5047365
  simp only [CollatzResearch.WordTrace]
  refine ⟨184092525359266101158087549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122728350239510734105391699 184092525359266101158087549)
  ·
    refine ⟨69034697009724787934282831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184092525359266101158087549 69034697009724787934282831)
    ·
      refine ⟨103552045514587181901424247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69034697009724787934282831 103552045514587181901424247)
      ·
        refine ⟨155328068271880772852136371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103552045514587181901424247 155328068271880772852136371)
        ·
          refine ⟨232992102407821159278204557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155328068271880772852136371 232992102407821159278204557)
          ·
            refine ⟨87372038402932934729326709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232992102407821159278204557 87372038402932934729326709)
            ·
              refine ⟨8191128600274962630874379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87372038402932934729326709 8191128600274962630874379)
              ·
                refine ⟨12286692900412443946311569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8191128600274962630874379 12286692900412443946311569)
                ·
                  refine ⟨9215019675309332959733677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12286692900412443946311569 9215019675309332959733677)
                  ·
                    refine ⟨3455632378240999859900129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9215019675309332959733677 3455632378240999859900129)
                    ·
                      refine ⟨2591724283680749894925097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455632378240999859900129 2591724283680749894925097)
                      ·
                        rfl

theorem cell23_5047365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_5047365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047365 prefixEnd_5047365 := by exact prefixLift 5047365
  have htrace : WordTrace (prefixWord ++ tailWord_5047365) baseStart_5047365 baseEnd_5047365 := by
    simpa [prefixWord, tailWord_5047365, baseEnd_5047365] using wordTrace_append hprefix tailTrace_5047365
  have hstable : (prefixWord ++ tailWord_5047365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047365).length < 2 ^ (prefixWord ++ tailWord_5047365).sum := by decide
  have hdescent : baseEnd_5047365 < baseStart_5047365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047389 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5047389 : Nat := 118140960795 + 5047389 * 2 ^ 59
def prefixEnd_5047389 : Nat := 4983230072969 + 3 ^ 40 * 5047389 * 2
def baseEnd_5047389 : Nat := 2591736607216457801024987

theorem tailTrace_5047389 : CollatzResearch.WordTrace tailWord_5047389 prefixEnd_5047389 2591736607216457801024987 := by
  unfold tailWord_5047389
  simp only [CollatzResearch.WordTrace]
  refine ⟨184093400711179153256961221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122728933807452768837974147 184093400711179153256961221)
  ·
    refine ⟨34517512633346091235680229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184093400711179153256961221 34517512633346091235680229)
    ·
      refine ⟨6472033618752392106690043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34517512633346091235680229 6472033618752392106690043)
      ·
        refine ⟨9708050428128588160035065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6472033618752392106690043 9708050428128588160035065)
        ·
          refine ⟨7281037821096441120026299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9708050428128588160035065 7281037821096441120026299)
          ·
            refine ⟨10921556731644661680039449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281037821096441120026299 10921556731644661680039449)
            ·
              refine ⟨8191167548733496260029587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10921556731644661680039449 8191167548733496260029587)
              ·
                refine ⟨12286751323100244390044381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8191167548733496260029587 12286751323100244390044381)
                ·
                  refine ⟨4607531746162591646266643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12286751323100244390044381 4607531746162591646266643)
                  ·
                    refine ⟨6911297619243887469399965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607531746162591646266643 6911297619243887469399965)
                    ·
                      refine ⟨2591736607216457801024987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911297619243887469399965 2591736607216457801024987)
                      ·
                        rfl

theorem cell23_5047389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5047389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047389 prefixEnd_5047389 := by exact prefixLift 5047389
  have htrace : WordTrace (prefixWord ++ tailWord_5047389) baseStart_5047389 baseEnd_5047389 := by
    simpa [prefixWord, tailWord_5047389, baseEnd_5047389] using wordTrace_append hprefix tailTrace_5047389
  have hstable : (prefixWord ++ tailWord_5047389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047389).length < 2 ^ (prefixWord ++ tailWord_5047389).sum := by decide
  have hdescent : baseEnd_5047389 < baseStart_5047389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047391 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5047391 : Nat := 118140960795 + 5047391 * 2 ^ 59
def prefixEnd_5047391 : Nat := 4983230072969 + 3 ^ 40 * 5047391 * 2
def baseEnd_5047391 : Nat := 2591737634177766793199977

theorem tailTrace_5047391 : CollatzResearch.WordTrace tailWord_5047391 prefixEnd_5047391 2591737634177766793199977 := by
  unfold tailWord_5047391
  simp only [CollatzResearch.WordTrace]
  refine ⟨184093473657171907598534027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122728982438114605065689351 184093473657171907598534027)
  ·
    refine ⟨276140210485757861397801041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184093473657171907598534027 276140210485757861397801041)
    ·
      refine ⟨207105157864318396048350781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276140210485757861397801041 207105157864318396048350781)
      ·
        refine ⟨77664434199119398518131543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207105157864318396048350781 77664434199119398518131543)
        ·
          refine ⟨116496651298679097777197315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77664434199119398518131543 116496651298679097777197315)
          ·
            refine ⟨174744976948018646665795973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116496651298679097777197315 174744976948018646665795973)
            ·
              refine ⟨32764683177753496249836745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174744976948018646665795973 32764683177753496249836745)
              ·
                refine ⟨24573512383315122187377559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32764683177753496249836745 24573512383315122187377559)
                ·
                  refine ⟨36860268574972683281066339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24573512383315122187377559 36860268574972683281066339)
                  ·
                    refine ⟨55290402862459024921599509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36860268574972683281066339 55290402862459024921599509)
                    ·
                      refine ⟨2591737634177766793199977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55290402862459024921599509 2591737634177766793199977)
                      ·
                        rfl

theorem cell23_5047391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5047391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047391 prefixEnd_5047391 := by exact prefixLift 5047391
  have htrace : WordTrace (prefixWord ++ tailWord_5047391) baseStart_5047391 baseEnd_5047391 := by
    simpa [prefixWord, tailWord_5047391, baseEnd_5047391] using wordTrace_append hprefix tailTrace_5047391
  have hstable : (prefixWord ++ tailWord_5047391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047391).length < 2 ^ (prefixWord ++ tailWord_5047391).sum := by decide
  have hdescent : baseEnd_5047391 < baseStart_5047391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047405 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5047405 : Nat := 118140960795 + 5047405 * 2 ^ 59
def prefixEnd_5047405 : Nat := 4983230072969 + 3 ^ 40 * 5047405 * 2
def baseEnd_5047405 : Nat := 863914940968976579474971

theorem tailTrace_5047405 : CollatzResearch.WordTrace tailWord_5047405 prefixEnd_5047405 863914940968976579474971 := by
  unfold tailWord_5047405
  simp only [CollatzResearch.WordTrace]
  refine ⟨184093984279121187989543669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122729322852747458659695779 184093984279121187989543669)
  ·
    refine ⟨17258811026167611374019719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184093984279121187989543669 17258811026167611374019719)
    ·
      refine ⟨25888216539251417061029579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17258811026167611374019719 25888216539251417061029579)
      ·
        refine ⟨38832324808877125591544369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25888216539251417061029579 38832324808877125591544369)
        ·
          refine ⟨29124243606657844193658277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38832324808877125591544369 29124243606657844193658277)
          ·
            refine ⟨5460795676248345786310927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29124243606657844193658277 5460795676248345786310927)
            ·
              refine ⟨8191193514372518679466391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5460795676248345786310927 8191193514372518679466391)
              ·
                refine ⟨12286790271558778019199587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8191193514372518679466391 12286790271558778019199587)
                ·
                  refine ⟨18430185407338167028799381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12286790271558778019199587 18430185407338167028799381)
                  ·
                    refine ⟨863914940968976579474971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18430185407338167028799381 863914940968976579474971)
                    ·
                      rfl

theorem cell23_5047405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5047405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047405 prefixEnd_5047405 := by exact prefixLift 5047405
  have htrace : WordTrace (prefixWord ++ tailWord_5047405) baseStart_5047405 baseEnd_5047405 := by
    simpa [prefixWord, tailWord_5047405, baseEnd_5047405] using wordTrace_append hprefix tailTrace_5047405
  have hstable : (prefixWord ++ tailWord_5047405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047405).length < 2 ^ (prefixWord ++ tailWord_5047405).sum := by decide
  have hdescent : baseEnd_5047405 < baseStart_5047405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047415 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_5047415 : Nat := 118140960795 + 5047415 * 2 ^ 59
def prefixEnd_5047415 : Nat := 4983230072969 + 3 ^ 40 * 5047415 * 2
def baseEnd_5047415 : Nat := 2591749957713474699299867

theorem tailTrace_5047415 : CollatzResearch.WordTrace tailWord_5047415 prefixEnd_5047415 2591749957713474699299867 := by
  unfold tailWord_5047415
  simp only [CollatzResearch.WordTrace]
  refine ⟨184094349009084959697407699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122729566006056639798271799 184094349009084959697407699)
  ·
    refine ⟨276141523513627439546111549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184094349009084959697407699 276141523513627439546111549)
    ·
      refine ⟨103553071317610289829791831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276141523513627439546111549 103553071317610289829791831)
      ·
        refine ⟨155329606976415434744687747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103553071317610289829791831 155329606976415434744687747)
        ·
          refine ⟨232994410464623152117031621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155329606976415434744687747 232994410464623152117031621)
          ·
            refine ⟨43686451962116841021943429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232994410464623152117031621 43686451962116841021943429)
            ·
              refine ⟨8191209742896907691614393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43686451962116841021943429 8191209742896907691614393)
              ·
                refine ⟨6143407307172680768710795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8191209742896907691614393 6143407307172680768710795)
                ·
                  refine ⟨9215110960759021153066193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143407307172680768710795 9215110960759021153066193)
                  ·
                    refine ⟨6911333220569265864799645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9215110960759021153066193 6911333220569265864799645)
                    ·
                      refine ⟨2591749957713474699299867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911333220569265864799645 2591749957713474699299867)
                      ·
                        rfl

theorem cell23_5047415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_5047415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047415 prefixEnd_5047415 := by exact prefixLift 5047415
  have htrace : WordTrace (prefixWord ++ tailWord_5047415) baseStart_5047415 baseEnd_5047415 := by
    simpa [prefixWord, tailWord_5047415, baseEnd_5047415] using wordTrace_append hprefix tailTrace_5047415
  have hstable : (prefixWord ++ tailWord_5047415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047415).length < 2 ^ (prefixWord ++ tailWord_5047415).sum := by decide
  have hdescent : baseEnd_5047415 < baseStart_5047415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047431 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 9]
def baseStart_5047431 : Nat := 118140960795 + 5047431 * 2 ^ 59
def prefixEnd_5047431 : Nat := 4983230072969 + 3 ^ 40 * 5047431 * 2
def baseEnd_5047431 : Nat := 863919391134648878899931

theorem tailTrace_5047431 : CollatzResearch.WordTrace tailWord_5047431 prefixEnd_5047431 863919391134648878899931 := by
  unfold tailWord_5047431
  simp only [CollatzResearch.WordTrace]
  refine ⟨184094932577026994429990147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122729955051351329619993431 184094932577026994429990147)
  ·
    refine ⟨276142398865540491644985221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184094932577026994429990147 276142398865540491644985221)
    ·
      refine ⟨51776699787288842183434729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276142398865540491644985221 51776699787288842183434729)
      ·
        refine ⟨38832524840466631637576047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51776699787288842183434729 38832524840466631637576047)
        ·
          refine ⟨58248787260699947456364071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38832524840466631637576047 58248787260699947456364071)
          ·
            refine ⟨87373180891049921184546107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58248787260699947456364071 87373180891049921184546107)
            ·
              refine ⟨131059771336574881776819161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87373180891049921184546107 131059771336574881776819161)
              ·
                refine ⟨98294828502431161332614371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131059771336574881776819161 98294828502431161332614371)
                ·
                  refine ⟨147442242753646741998921557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98294828502431161332614371 147442242753646741998921557)
                  ·
                    refine ⟨863919391134648878899931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147442242753646741998921557 863919391134648878899931)
                    ·
                      rfl

theorem cell23_5047431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_5047431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047431 prefixEnd_5047431 := by exact prefixLift 5047431
  have htrace : WordTrace (prefixWord ++ tailWord_5047431) baseStart_5047431 baseEnd_5047431 := by
    simpa [prefixWord, tailWord_5047431, baseEnd_5047431] using wordTrace_append hprefix tailTrace_5047431
  have hstable : (prefixWord ++ tailWord_5047431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047431).length < 2 ^ (prefixWord ++ tailWord_5047431).sum := by decide
  have hdescent : baseEnd_5047431 < baseStart_5047431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047485 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_5047485 : Nat := 118140960795 + 5047485 * 2 ^ 59
def prefixEnd_5047485 : Nat := 4983230072969 + 3 ^ 40 * 5047485 * 2
def baseEnd_5047485 : Nat := 2591785901359289425424545

theorem tailTrace_5047485 : CollatzResearch.WordTrace tailWord_5047485 prefixEnd_5047485 2591785901359289425424545 := by
  unfold tailWord_5047485
  simp only [CollatzResearch.WordTrace]
  refine ⟨184096902118831361652455909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122731268079220907768303939 184096902118831361652455909)
  ·
    refine ⟨34518169147280880309835483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184096902118831361652455909 34518169147280880309835483)
    ·
      refine ⟨51777253720921320464753225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34518169147280880309835483 51777253720921320464753225)
      ·
        refine ⟨38832940290690990348564919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51777253720921320464753225 38832940290690990348564919)
        ·
          refine ⟨58249410436036485522847379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38832940290690990348564919 58249410436036485522847379)
          ·
            refine ⟨87374115654054728284271069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58249410436036485522847379 87374115654054728284271069)
            ·
              refine ⟨32765293370270523106601651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87374115654054728284271069 32765293370270523106601651)
              ·
                refine ⟨49147940055405784659902477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32765293370270523106601651 49147940055405784659902477)
                ·
                  refine ⟨18430477520777169247463429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49147940055405784659902477 18430477520777169247463429)
                  ·
                    refine ⟨3455714535145719233899393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18430477520777169247463429 3455714535145719233899393)
                    ·
                      refine ⟨2591785901359289425424545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455714535145719233899393 2591785901359289425424545)
                      ·
                        rfl

theorem cell23_5047485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_5047485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047485 prefixEnd_5047485 := by exact prefixLift 5047485
  have htrace : WordTrace (prefixWord ++ tailWord_5047485) baseStart_5047485 baseEnd_5047485 := by
    simpa [prefixWord, tailWord_5047485, baseEnd_5047485] using wordTrace_append hprefix tailTrace_5047485
  have hstable : (prefixWord ++ tailWord_5047485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047485).length < 2 ^ (prefixWord ++ tailWord_5047485).sum := by decide
  have hdescent : baseEnd_5047485 < baseStart_5047485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047491 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 11]
def baseStart_5047491 : Nat := 118140960795 + 5047491 * 2 ^ 59
def prefixEnd_5047491 : Nat := 4983230072969 + 3 ^ 40 * 5047491 * 2
def baseEnd_5047491 : Nat := 287976553582579600216613

theorem tailTrace_5047491 : CollatzResearch.WordTrace tailWord_5047491 prefixEnd_5047491 287976553582579600216613 := by
  unfold tailWord_5047491
  simp only [CollatzResearch.WordTrace]
  refine ⟨184097120956809624677174327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122731413971206416451449551 184097120956809624677174327)
  ·
    refine ⟨276145681435214437015761491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184097120956809624677174327 276145681435214437015761491)
    ·
      refine ⟨414218522152821655523642237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276145681435214437015761491 414218522152821655523642237)
      ·
        refine ⟨155331945807308120821365839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414218522152821655523642237 155331945807308120821365839)
        ·
          refine ⟨232997918710962181232048759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155331945807308120821365839 232997918710962181232048759)
          ·
            refine ⟨349496878066443271848073139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232997918710962181232048759 349496878066443271848073139)
            ·
              refine ⟨524245317099664907772109709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349496878066443271848073139 524245317099664907772109709)
              ·
                refine ⟨196591993912374340414541141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524245317099664907772109709 196591993912374340414541141)
                ·
                  refine ⟨287976553582579600216613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 196591993912374340414541141 287976553582579600216613)
                  ·
                    rfl

theorem cell23_5047491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 11].length) (baseStart_5047491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047491 prefixEnd_5047491 := by exact prefixLift 5047491
  have htrace : WordTrace (prefixWord ++ tailWord_5047491) baseStart_5047491 baseEnd_5047491 := by
    simpa [prefixWord, tailWord_5047491, baseEnd_5047491] using wordTrace_append hprefix tailTrace_5047491
  have hstable : (prefixWord ++ tailWord_5047491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047491).length < 2 ^ (prefixWord ++ tailWord_5047491).sum := by decide
  have hdescent : baseEnd_5047491 < baseStart_5047491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047525 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 7]
def baseStart_5047525 : Nat := 118140960795 + 5047525 * 2 ^ 59
def prefixEnd_5047525 : Nat := 4983230072969 + 3 ^ 40 * 5047525 * 2
def baseEnd_5047525 : Nat := 287978493398385474324929

theorem tailTrace_5047525 : CollatzResearch.WordTrace tailWord_5047525 prefixEnd_5047525 287978493398385474324929 := by
  unfold tailWord_5047525
  simp only [CollatzResearch.WordTrace]
  refine ⟨184098361038686448483912029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122732240692457632322608019 184098361038686448483912029)
  ·
    refine ⟨69036885389507418181467011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184098361038686448483912029 69036885389507418181467011)
    ·
      refine ⟨103555328084261127272200517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69036885389507418181467011 103555328084261127272200517)
      ·
        refine ⟨19416624015798961363537597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103555328084261127272200517 19416624015798961363537597)
        ·
          refine ⟨7281234005924610511326599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19416624015798961363537597 7281234005924610511326599)
          ·
            refine ⟨10921851008886915766989899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281234005924610511326599 10921851008886915766989899)
            ·
              refine ⟨16382776513330373650484849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10921851008886915766989899 16382776513330373650484849)
              ·
                refine ⟨12287082384997780237863637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16382776513330373650484849 12287082384997780237863637)
                ·
                  refine ⟨287978493398385474324929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12287082384997780237863637 287978493398385474324929)
                  ·
                    rfl

theorem cell23_5047525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_5047525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047525 prefixEnd_5047525 := by exact prefixLift 5047525
  have htrace : WordTrace (prefixWord ++ tailWord_5047525) baseStart_5047525 baseEnd_5047525 := by
    simpa [prefixWord, tailWord_5047525, baseEnd_5047525] using wordTrace_append hprefix tailTrace_5047525
  have hstable : (prefixWord ++ tailWord_5047525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047525).length < 2 ^ (prefixWord ++ tailWord_5047525).sum := by decide
  have hdescent : baseEnd_5047525 < baseStart_5047525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047570 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5047570 : Nat := 118140960795 + 5047570 * 2 ^ 59
def prefixEnd_5047570 : Nat := 4983230072969 + 3 ^ 40 * 5047570 * 2
def baseEnd_5047570 : Nat := 2591829547214921592861655

theorem tailTrace_5047570 : CollatzResearch.WordTrace tailWord_5047570 prefixEnd_5047570 2591829547214921592861655 := by
  unfold tailWord_5047570
  simp only [CollatzResearch.WordTrace]
  refine ⟨46025000580880855292325041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122733334882348947446200109 46025000580880855292325041)
  ·
    refine ⟨34518750435660641469243781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46025000580880855292325041 34518750435660641469243781)
    ·
      refine ⟨6472265706686370275483209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34518750435660641469243781 6472265706686370275483209)
      ·
        refine ⟨4854199280014777706612407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6472265706686370275483209 4854199280014777706612407)
        ·
          refine ⟨7281298920022166559918611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854199280014777706612407 7281298920022166559918611)
          ·
            refine ⟨10921948380033249839877917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281298920022166559918611 10921948380033249839877917)
            ·
              refine ⟨4095730642512468689954219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10921948380033249839877917 4095730642512468689954219)
              ·
                refine ⟨6143595963768703034931329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4095730642512468689954219 6143595963768703034931329)
                ·
                  refine ⟨4607696972826527276198497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6143595963768703034931329 4607696972826527276198497)
                  ·
                    refine ⟨3455772729619895457148873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607696972826527276198497 3455772729619895457148873)
                    ·
                      refine ⟨2591829547214921592861655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455772729619895457148873 2591829547214921592861655)
                      ·
                        rfl

theorem cell23_5047570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5047570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047570 prefixEnd_5047570 := by exact prefixLift 5047570
  have htrace : WordTrace (prefixWord ++ tailWord_5047570) baseStart_5047570 baseEnd_5047570 := by
    simpa [prefixWord, tailWord_5047570, baseEnd_5047570] using wordTrace_append hprefix tailTrace_5047570
  have hstable : (prefixWord ++ tailWord_5047570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047570).length < 2 ^ (prefixWord ++ tailWord_5047570).sum := by decide
  have hdescent : baseEnd_5047570 < baseStart_5047570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047612 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_5047612 : Nat := 118140960795 + 5047612 * 2 ^ 59
def prefixEnd_5047612 : Nat := 4983230072969 + 3 ^ 40 * 5047612 * 2
def baseEnd_5047612 : Nat := 2591851113402410428536461

theorem tailTrace_5047612 : CollatzResearch.WordTrace tailWord_5047612 prefixEnd_5047612 2591851113402410428536461 := by
  unfold tailWord_5047612
  simp only [CollatzResearch.WordTrace]
  refine ⟨92050767094685631171164545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122734356126247508228219393 92050767094685631171164545)
  ·
    refine ⟨69038075321014223378373409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92050767094685631171164545 69038075321014223378373409)
    ·
      refine ⟨51778556490760667533780057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69038075321014223378373409 51778556490760667533780057)
      ·
        refine ⟨38833917368070500650335043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51778556490760667533780057 38833917368070500650335043)
        ·
          refine ⟨58250876052105750975502565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38833917368070500650335043 58250876052105750975502565)
          ·
            refine ⟨10922039259769828307906731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58250876052105750975502565 10922039259769828307906731)
            ·
              refine ⟨16383058889654742461860097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10922039259769828307906731 16383058889654742461860097)
              ·
                refine ⟨12287294167241056846395073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16383058889654742461860097 12287294167241056846395073)
                ·
                  refine ⟨9215470625430792634796305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12287294167241056846395073 9215470625430792634796305)
                  ·
                    refine ⟨6911602969073094476097229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9215470625430792634796305 6911602969073094476097229)
                    ·
                      refine ⟨2591851113402410428536461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911602969073094476097229 2591851113402410428536461)
                      ·
                        rfl

theorem cell23_5047612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_5047612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047612 prefixEnd_5047612 := by exact prefixLift 5047612
  have htrace : WordTrace (prefixWord ++ tailWord_5047612) baseStart_5047612 baseEnd_5047612 := by
    simpa [prefixWord, tailWord_5047612, baseEnd_5047612] using wordTrace_append hprefix tailTrace_5047612
  have hstable : (prefixWord ++ tailWord_5047612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047612).length < 2 ^ (prefixWord ++ tailWord_5047612).sum := by decide
  have hdescent : baseEnd_5047612 < baseStart_5047612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047642 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_5047642 : Nat := 118140960795 + 5047642 * 2 ^ 59
def prefixEnd_5047642 : Nat := 4983230072969 + 3 ^ 40 * 5047642 * 2
def baseEnd_5047642 : Nat := 2591866517822045311161323

theorem tailTrace_5047642 : CollatzResearch.WordTrace tailWord_5047642 prefixEnd_5047642 2591866517822045311161323 := by
  unfold tailWord_5047642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46025657094815644366480295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122735085586175051643947453 46025657094815644366480295)
  ·
    refine ⟨69038485642223466549720443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46025657094815644366480295 69038485642223466549720443)
    ·
      refine ⟨103557728463335199824580665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69038485642223466549720443 103557728463335199824580665)
      ·
        refine ⟨77668296347501399868435499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103557728463335199824580665 77668296347501399868435499)
        ·
          refine ⟨116502444521252099802653249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77668296347501399868435499 116502444521252099802653249)
          ·
            refine ⟨87376833390939074851989937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116502444521252099802653249 87376833390939074851989937)
            ·
              refine ⟨65532625043204306138992453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87376833390939074851989937 65532625043204306138992453)
              ·
                refine ⟨12287367195600807401061085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65532625043204306138992453 12287367195600807401061085)
                ·
                  refine ⟨4607762698350302775397907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12287367195600807401061085 4607762698350302775397907)
                  ·
                    refine ⟨6911644047525454163096861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607762698350302775397907 6911644047525454163096861)
                    ·
                      refine ⟨2591866517822045311161323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911644047525454163096861 2591866517822045311161323)
                      ·
                        rfl

theorem cell23_5047642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_5047642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047642 prefixEnd_5047642 := by exact prefixLift 5047642
  have htrace : WordTrace (prefixWord ++ tailWord_5047642) baseStart_5047642 baseEnd_5047642 := by
    simpa [prefixWord, tailWord_5047642, baseEnd_5047642] using wordTrace_append hprefix tailTrace_5047642
  have hstable : (prefixWord ++ tailWord_5047642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047642).length < 2 ^ (prefixWord ++ tailWord_5047642).sum := by decide
  have hdescent : baseEnd_5047642 < baseStart_5047642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047685 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_5047685 : Nat := 118140960795 + 5047685 * 2 ^ 59
def prefixEnd_5047685 : Nat := 4983230072969 + 3 ^ 40 * 5047685 * 2
def baseEnd_5047685 : Nat := 2591888597490188642923625

theorem tailTrace_5047685 : CollatzResearch.WordTrace tailWord_5047685 prefixEnd_5047685 2591888597490188642923625 := by
  unfold tailWord_5047685
  simp only [CollatzResearch.WordTrace]
  refine ⟨184104196718106795809736509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122736131145404530539824339 184104196718106795809736509)
  ·
    refine ⟨69039073769290048428651191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184104196718106795809736509 69039073769290048428651191)
    ·
      refine ⟨103558610653935072642976787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69039073769290048428651191 103558610653935072642976787)
      ·
        refine ⟨155337915980902608964465181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103558610653935072642976787 155337915980902608964465181)
        ·
          refine ⟨58251718492838478361674443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155337915980902608964465181 58251718492838478361674443)
          ·
            refine ⟨87377577739257717542511665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58251718492838478361674443 87377577739257717542511665)
            ·
              refine ⟨65533183304443288156883749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87377577739257717542511665 65533183304443288156883749)
              ·
                refine ⟨12287471869583116529415703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65533183304443288156883749 12287471869583116529415703)
                ·
                  refine ⟨18431207804374674794123555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12287471869583116529415703 18431207804374674794123555)
                  ·
                    refine ⟨27646811706562012191185333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18431207804374674794123555 27646811706562012191185333)
                    ·
                      refine ⟨2591888597490188642923625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27646811706562012191185333 2591888597490188642923625)
                      ·
                        rfl

theorem cell23_5047685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_5047685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047685 prefixEnd_5047685 := by exact prefixLift 5047685
  have htrace : WordTrace (prefixWord ++ tailWord_5047685) baseStart_5047685 baseEnd_5047685 := by
    simpa [prefixWord, tailWord_5047685, baseEnd_5047685] using wordTrace_append hprefix tailTrace_5047685
  have hstable : (prefixWord ++ tailWord_5047685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047685).length < 2 ^ (prefixWord ++ tailWord_5047685).sum := by decide
  have hdescent : baseEnd_5047685 < baseStart_5047685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047692 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_5047692 : Nat := 118140960795 + 5047692 * 2 ^ 59
def prefixEnd_5047692 : Nat := 4983230072969 + 3 ^ 40 * 5047692 * 2
def baseEnd_5047692 : Nat := 863964063951590038512031

theorem tailTrace_5047692 : CollatzResearch.WordTrace tailWord_5047692 prefixEnd_5047692 863964063951590038512031 := by
  unfold tailWord_5047692
  simp only [CollatzResearch.WordTrace]
  refine ⟨92052226014540718002620665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122736301352720957336827553 92052226014540718002620665)
  ·
    refine ⟨69039169510905538501965499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92052226014540718002620665 69039169510905538501965499)
    ·
      refine ⟨103558754266358307752948249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69039169510905538501965499 103558754266358307752948249)
      ·
        refine ⟨77669065699768730814711187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103558754266358307752948249 77669065699768730814711187)
        ·
          refine ⟨116503598549653096222066781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77669065699768730814711187 116503598549653096222066781)
          ·
            refine ⟨43688849456119911083275043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116503598549653096222066781 43688849456119911083275043)
            ·
              refine ⟨65533274184179866624912565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43688849456119911083275043 65533274184179866624912565)
              ·
                refine ⟨6143744454766862496085553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65533274184179866624912565 6143744454766862496085553)
                ·
                  refine ⟨4607808341075146872064165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6143744454766862496085553 4607808341075146872064165)
                  ·
                    refine ⟨863964063951590038512031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4607808341075146872064165 863964063951590038512031)
                    ·
                      rfl

theorem cell23_5047692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_5047692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047692 prefixEnd_5047692 := by exact prefixLift 5047692
  have htrace : WordTrace (prefixWord ++ tailWord_5047692) baseStart_5047692 baseEnd_5047692 := by
    simpa [prefixWord, tailWord_5047692, baseEnd_5047692] using wordTrace_append hprefix tailTrace_5047692
  have hstable : (prefixWord ++ tailWord_5047692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047692).length < 2 ^ (prefixWord ++ tailWord_5047692).sum := by decide
  have hdescent : baseEnd_5047692 < baseStart_5047692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047710 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5047710 : Nat := 118140960795 + 5047710 * 2 ^ 59
def prefixEnd_5047710 : Nat := 4983230072969 + 3 ^ 40 * 5047710 * 2
def baseEnd_5047710 : Nat := 2591901434506551045111011

theorem tailTrace_5047710 : CollatzResearch.WordTrace tailWord_5047710 prefixEnd_5047710 2591901434506551045111011 := by
  unfold tailWord_5047710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013138567877028134924573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122736739028677483386264389 23013138567877028134924573)
  ·
    refine ⟨8629926962953885550596715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23013138567877028134924573 8629926962953885550596715)
    ·
      refine ⟨12944890444430828325895073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8629926962953885550596715 12944890444430828325895073)
      ·
        refine ⟨9708667833323121244421305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12944890444430828325895073 9708667833323121244421305)
        ·
          refine ⟨7281500874992340933315979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9708667833323121244421305 7281500874992340933315979)
          ·
            refine ⟨10922251312488511399973969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281500874992340933315979 10922251312488511399973969)
            ·
              refine ⟨8191688484366383549980477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10922251312488511399973969 8191688484366383549980477)
              ·
                refine ⟨3071883181637393831242679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8191688484366383549980477 3071883181637393831242679)
                ·
                  refine ⟨4607824772456090746864019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071883181637393831242679 4607824772456090746864019)
                  ·
                    refine ⟨6911737158684136120296029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607824772456090746864019 6911737158684136120296029)
                    ·
                      refine ⟨2591901434506551045111011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911737158684136120296029 2591901434506551045111011)
                      ·
                        rfl

theorem cell23_5047710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5047710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047710 prefixEnd_5047710 := by exact prefixLift 5047710
  have htrace : WordTrace (prefixWord ++ tailWord_5047710) baseStart_5047710 baseEnd_5047710 := by
    simpa [prefixWord, tailWord_5047710, baseEnd_5047710] using wordTrace_append hprefix tailTrace_5047710
  have hstable : (prefixWord ++ tailWord_5047710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047710).length < 2 ^ (prefixWord ++ tailWord_5047710).sum := by decide
  have hdescent : baseEnd_5047710 < baseStart_5047710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047719 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5047719 : Nat := 118140960795 + 5047719 * 2 ^ 59
def prefixEnd_5047719 : Nat := 4983230072969 + 3 ^ 40 * 5047719 * 2
def baseEnd_5047719 : Nat := 2591906055832441509898469

theorem tailTrace_5047719 : CollatzResearch.WordTrace tailWord_5047719 prefixEnd_5047719 2591906055832441509898469 := by
  unfold tailWord_5047719
  simp only [CollatzResearch.WordTrace]
  refine ⟨184105436799983619616474211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122736957866655746410982807 184105436799983619616474211)
  ·
    refine ⟨276158155199975429424711317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184105436799983619616474211 276158155199975429424711317)
    ·
      refine ⟨12944913524998848254283343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 276158155199975429424711317 12944913524998848254283343)
      ·
        refine ⟨19417370287498272381425015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12944913524998848254283343 19417370287498272381425015)
        ·
          refine ⟨29126055431247408572137523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19417370287498272381425015 29126055431247408572137523)
          ·
            refine ⟨43689083146871112858206285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29126055431247408572137523 43689083146871112858206285)
            ·
              refine ⟨16383406180076667321827357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43689083146871112858206285 16383406180076667321827357)
              ·
                refine ⟨6143777317528750245685259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16383406180076667321827357 6143777317528750245685259)
                ·
                  refine ⟨9215665976293125368527889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143777317528750245685259 9215665976293125368527889)
                  ·
                    refine ⟨6911749482219844026395917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9215665976293125368527889 6911749482219844026395917)
                    ·
                      refine ⟨2591906055832441509898469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911749482219844026395917 2591906055832441509898469)
                      ·
                        rfl

theorem cell23_5047719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5047719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047719 prefixEnd_5047719 := by exact prefixLift 5047719
  have htrace : WordTrace (prefixWord ++ tailWord_5047719) baseStart_5047719 baseEnd_5047719 := by
    simpa [prefixWord, tailWord_5047719, baseEnd_5047719] using wordTrace_append hprefix tailTrace_5047719
  have hstable : (prefixWord ++ tailWord_5047719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047719).length < 2 ^ (prefixWord ++ tailWord_5047719).sum := by decide
  have hdescent : baseEnd_5047719 < baseStart_5047719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047733 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_5047733 : Nat := 118140960795 + 5047733 * 2 ^ 59
def prefixEnd_5047733 : Nat := 4983230072969 + 3 ^ 40 * 5047733 * 2
def baseEnd_5047733 : Nat := 2591913244561604455123405

theorem tailTrace_5047733 : CollatzResearch.WordTrace tailWord_5047733 prefixEnd_5047733 2591913244561604455123405 := by
  unfold tailWord_5047733
  simp only [CollatzResearch.WordTrace]
  refine ⟨184105947421932900007483853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122737298281288600004989235 184105947421932900007483853)
  ·
    refine ⟨69039730283224837502806445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184105947421932900007483853 69039730283224837502806445)
    ·
      refine ⟨25889898856209314063552417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69039730283224837502806445 25889898856209314063552417)
      ·
        refine ⟨19417424142156985547664313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25889898856209314063552417 19417424142156985547664313)
        ·
          refine ⟨14563068106617739160748235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19417424142156985547664313 14563068106617739160748235)
          ·
            refine ⟨21844602159926608741122353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14563068106617739160748235 21844602159926608741122353)
            ·
              refine ⟨16383451619944956555841765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21844602159926608741122353 16383451619944956555841765)
              ·
                refine ⟨3071897178739679354220331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16383451619944956555841765 3071897178739679354220331)
                ·
                  refine ⟨4607845768109519031330497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071897178739679354220331 4607845768109519031330497)
                  ·
                    refine ⟨3455884326082139273497873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4607845768109519031330497 3455884326082139273497873)
                    ·
                      refine ⟨2591913244561604455123405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455884326082139273497873 2591913244561604455123405)
                      ·
                        rfl

theorem cell23_5047733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_5047733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047733 prefixEnd_5047733 := by exact prefixLift 5047733
  have htrace : WordTrace (prefixWord ++ tailWord_5047733) baseStart_5047733 baseEnd_5047733 := by
    simpa [prefixWord, tailWord_5047733, baseEnd_5047733] using wordTrace_append hprefix tailTrace_5047733
  have hstable : (prefixWord ++ tailWord_5047733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047733).length < 2 ^ (prefixWord ++ tailWord_5047733).sum := by decide
  have hdescent : baseEnd_5047733 < baseStart_5047733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047755 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_5047755 : Nat := 118140960795 + 5047755 * 2 ^ 59
def prefixEnd_5047755 : Nat := 4983230072969 + 3 ^ 40 * 5047755 * 2
def baseEnd_5047755 : Nat := 2591924541136003369048303

theorem tailTrace_5047755 : CollatzResearch.WordTrace tailWord_5047755 prefixEnd_5047755 2591924541136003369048303 := by
  unfold tailWord_5047755
  simp only [CollatzResearch.WordTrace]
  refine ⟨184106749827853197764784719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122737833218568798509856479 184106749827853197764784719)
  ·
    refine ⟨276160124741779796647177079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184106749827853197764784719 276160124741779796647177079)
    ·
      refine ⟨414240187112669694970765619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276160124741779796647177079 414240187112669694970765619)
      ·
        refine ⟨621360280669004542456148429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414240187112669694970765619 621360280669004542456148429)
        ·
          refine ⟨233010105250876703421055661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621360280669004542456148429 233010105250876703421055661)
          ·
            refine ⟨87378789469078763782895873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233010105250876703421055661 87378789469078763782895873)
            ·
              refine ⟨65534092101809072837171905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87378789469078763782895873 65534092101809072837171905)
              ·
                refine ⟨49150569076356804627878929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65534092101809072837171905 49150569076356804627878929)
                ·
                  refine ⟨36862926807267603470909197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49150569076356804627878929 36862926807267603470909197)
                  ·
                    refine ⟨13823597552725351301590949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36862926807267603470909197 13823597552725351301590949)
                    ·
                      refine ⟨2591924541136003369048303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13823597552725351301590949 2591924541136003369048303)
                      ·
                        rfl

theorem cell23_5047755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_5047755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047755 prefixEnd_5047755 := by exact prefixLift 5047755
  have htrace : WordTrace (prefixWord ++ tailWord_5047755) baseStart_5047755 baseEnd_5047755 := by
    simpa [prefixWord, tailWord_5047755, baseEnd_5047755] using wordTrace_append hprefix tailTrace_5047755
  have hstable : (prefixWord ++ tailWord_5047755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047755).length < 2 ^ (prefixWord ++ tailWord_5047755).sum := by decide
  have hdescent : baseEnd_5047755 < baseStart_5047755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047759 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 1, 3, 2]
def baseStart_5047759 : Nat := 118140960795 + 5047759 * 2 ^ 59
def prefixEnd_5047759 : Nat := 4983230072969 + 3 ^ 40 * 5047759 * 2
def baseEnd_5047759 : Nat := 2591926595058621353398285

theorem tailTrace_5047759 : CollatzResearch.WordTrace tailWord_5047759 prefixEnd_5047759 2591926595058621353398285 := by
  unfold tailWord_5047759
  simp only [CollatzResearch.WordTrace]
  refine ⟨184106895719838706447930331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122737930479892470965286887 184106895719838706447930331)
  ·
    refine ⟨276160343579758059671895497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184106895719838706447930331 276160343579758059671895497)
    ·
      refine ⟨207120257684818544753921623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276160343579758059671895497 207120257684818544753921623)
      ·
        refine ⟨310680386527227817130882435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207120257684818544753921623 310680386527227817130882435)
        ·
          refine ⟨466020579790841725696323653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310680386527227817130882435 466020579790841725696323653)
          ·
            refine ⟨87378858710782823568060685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 466020579790841725696323653 87378858710782823568060685)
            ·
              refine ⟨32767072016543558838022757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87378858710782823568060685 32767072016543558838022757)
              ·
                refine ⟨6143826003101917282129267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32767072016543558838022757 6143826003101917282129267)
                ·
                  refine ⟨9215739004652875923193901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143826003101917282129267 9215739004652875923193901)
                  ·
                    refine ⟨3455902126744828471197713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9215739004652875923193901 3455902126744828471197713)
                    ·
                      refine ⟨2591926595058621353398285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455902126744828471197713 2591926595058621353398285)
                      ·
                        rfl

theorem cell23_5047759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3, 2].length) (baseStart_5047759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047759 prefixEnd_5047759 := by exact prefixLift 5047759
  have htrace : WordTrace (prefixWord ++ tailWord_5047759) baseStart_5047759 baseEnd_5047759 := by
    simpa [prefixWord, tailWord_5047759, baseEnd_5047759] using wordTrace_append hprefix tailTrace_5047759
  have hstable : (prefixWord ++ tailWord_5047759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047759).length < 2 ^ (prefixWord ++ tailWord_5047759).sum := by decide
  have hdescent : baseEnd_5047759 < baseStart_5047759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047766 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5047766 : Nat := 118140960795 + 5047766 * 2 ^ 59
def prefixEnd_5047766 : Nat := 4983230072969 + 3 ^ 40 * 5047766 * 2
def baseEnd_5047766 : Nat := 2591930189423202826010753

theorem tailTrace_5047766 : CollatzResearch.WordTrace tailWord_5047766 prefixEnd_5047766 2591930189423202826010753 := by
  unfold tailWord_5047766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506696939425834165214697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122738100687208897762290101 11506696939425834165214697)
  ·
    refine ⟨8630022704569375623911023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11506696939425834165214697 8630022704569375623911023)
    ·
      refine ⟨12945034056854063435866535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630022704569375623911023 12945034056854063435866535)
      ·
        refine ⟨19417551085281095153799803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12945034056854063435866535 19417551085281095153799803)
        ·
          refine ⟨29126326627921642730699705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19417551085281095153799803 29126326627921642730699705)
          ·
            refine ⟨21844744970941232048024779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29126326627921642730699705 21844744970941232048024779)
            ·
              refine ⟨32767117456411848072037169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21844744970941232048024779 32767117456411848072037169)
              ·
                refine ⟨24575338092308886054027877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32767117456411848072037169 24575338092308886054027877)
                ·
                  refine ⟨4607875892307916135130227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24575338092308886054027877 4607875892307916135130227)
                  ·
                    refine ⟨6911813838461874202695341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4607875892307916135130227 6911813838461874202695341)
                    ·
                      refine ⟨2591930189423202826010753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6911813838461874202695341 2591930189423202826010753)
                      ·
                        rfl

theorem cell23_5047766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5047766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047766 prefixEnd_5047766 := by exact prefixLift 5047766
  have htrace : WordTrace (prefixWord ++ tailWord_5047766) baseStart_5047766 baseEnd_5047766 := by
    simpa [prefixWord, tailWord_5047766, baseEnd_5047766] using wordTrace_append hprefix tailTrace_5047766
  have hstable : (prefixWord ++ tailWord_5047766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047766).length < 2 ^ (prefixWord ++ tailWord_5047766).sum := by decide
  have hdescent : baseEnd_5047766 < baseStart_5047766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047795 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 7]
def baseStart_5047795 : Nat := 118140960795 + 5047795 * 2 ^ 59
def prefixEnd_5047795 : Nat := 4983230072969 + 3 ^ 40 * 5047795 * 2
def baseEnd_5047795 : Nat := 287993897818020356949791

theorem tailTrace_5047795 : CollatzResearch.WordTrace tailWord_5047795 prefixEnd_5047795 287993897818020356949791 := by
  unfold tailWord_5047795
  simp only [CollatzResearch.WordTrace]
  refine ⟨184108208747708284596240839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122738805831805523064160559 184108208747708284596240839)
  ·
    refine ⟨276162313121562426894361259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184108208747708284596240839 276162313121562426894361259)
    ·
      refine ⟨414243469682343640341541889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276162313121562426894361259 414243469682343640341541889)
      ·
        refine ⟨310682602261757730256156417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414243469682343640341541889 310682602261757730256156417)
        ·
          refine ⟨233011951696318297692117313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310682602261757730256156417 233011951696318297692117313)
          ·
            refine ⟨174758963772238723269087985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233011951696318297692117313 174758963772238723269087985)
            ·
              refine ⟨131069222829179042451815989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174758963772238723269087985 131069222829179042451815989)
              ·
                refine ⟨12287739640235535229857749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131069222829179042451815989 12287739640235535229857749)
                ·
                  refine ⟨287993897818020356949791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12287739640235535229857749 287993897818020356949791)
                  ·
                    rfl

theorem cell23_5047795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 7].length) (baseStart_5047795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047795 prefixEnd_5047795 := by exact prefixLift 5047795
  have htrace : WordTrace (prefixWord ++ tailWord_5047795) baseStart_5047795 baseEnd_5047795 := by
    simpa [prefixWord, tailWord_5047795, baseEnd_5047795] using wordTrace_append hprefix tailTrace_5047795
  have hstable : (prefixWord ++ tailWord_5047795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047795).length < 2 ^ (prefixWord ++ tailWord_5047795).sum := by decide
  have hdescent : baseEnd_5047795 < baseStart_5047795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047810 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5047810 : Nat := 118140960795 + 5047810 * 2 ^ 59
def prefixEnd_5047810 : Nat := 4983230072969 + 3 ^ 40 * 5047810 * 2
def baseEnd_5047810 : Nat := 2591952782572000653860551

theorem tailTrace_5047810 : CollatzResearch.WordTrace tailWord_5047810 prefixEnd_5047810 2591952782572000653860551 := by
  unfold tailWord_5047810
  simp only [CollatzResearch.WordTrace]
  refine ⟨46027188960663485539509221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122739170561769294772024589 46027188960663485539509221)
  ·
    refine ⟨8630097930124403538657979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46027188960663485539509221 8630097930124403538657979)
    ·
      refine ⟨12945146895186605307986969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8630097930124403538657979 12945146895186605307986969)
      ·
        refine ⟨9708860171389953980990227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12945146895186605307986969 9708860171389953980990227)
        ·
          refine ⟨14563290257084930971485341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9708860171389953980990227 14563290257084930971485341)
          ·
            refine ⟨5461233846406849114307003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14563290257084930971485341 5461233846406849114307003)
            ·
              refine ⟨8191850769610273671460505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461233846406849114307003 8191850769610273671460505)
              ·
                refine ⟨6143888077207705253595379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8191850769610273671460505 6143888077207705253595379)
                ·
                  refine ⟨9215832115811557880393069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6143888077207705253595379 9215832115811557880393069)
                  ·
                    refine ⟨3455937043429334205147401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9215832115811557880393069 3455937043429334205147401)
                    ·
                      refine ⟨2591952782572000653860551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3455937043429334205147401 2591952782572000653860551)
                      ·
                        rfl

theorem cell23_5047810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5047810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047810 prefixEnd_5047810 := by exact prefixLift 5047810
  have htrace : WordTrace (prefixWord ++ tailWord_5047810) baseStart_5047810 baseEnd_5047810 := by
    simpa [prefixWord, tailWord_5047810, baseEnd_5047810] using wordTrace_append hprefix tailTrace_5047810
  have hstable : (prefixWord ++ tailWord_5047810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047810).length < 2 ^ (prefixWord ++ tailWord_5047810).sum := by decide
  have hdescent : baseEnd_5047810 < baseStart_5047810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047879 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_5047879 : Nat := 118140960795 + 5047879 * 2 ^ 59
def prefixEnd_5047879 : Nat := 4983230072969 + 3 ^ 40 * 5047879 * 2
def baseEnd_5047879 : Nat := 2591988212737160883897733

theorem tailTrace_5047879 : CollatzResearch.WordTrace tailWord_5047879 prefixEnd_5047879 2591988212737160883897733 := by
  unfold tailWord_5047879
  simp only [CollatzResearch.WordTrace]
  refine ⟨184111272479403966942298691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122740848319602644628199127 184111272479403966942298691)
  ·
    refine ⟨276166908719105950413448037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184111272479403966942298691 276166908719105950413448037)
    ·
      refine ⟨51781295384832365702521507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 276166908719105950413448037 51781295384832365702521507)
      ·
        refine ⟨77671943077248548553782261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51781295384832365702521507 77671943077248548553782261)
        ·
          refine ⟨7281744663492051426917087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77671943077248548553782261 7281744663492051426917087)
          ·
            refine ⟨10922616995238077140375631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281744663492051426917087 10922616995238077140375631)
            ·
              refine ⟨16383925492857115710563447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10922616995238077140375631 16383925492857115710563447)
              ·
                refine ⟨24575888239285673565845171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16383925492857115710563447 24575888239285673565845171)
                ·
                  refine ⟨36863832358928510348767757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24575888239285673565845171 36863832358928510348767757)
                  ·
                    refine ⟨13823937134598191380787909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36863832358928510348767757 13823937134598191380787909)
                    ·
                      refine ⟨2591988212737160883897733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13823937134598191380787909 2591988212737160883897733)
                      ·
                        rfl

theorem cell23_5047879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_5047879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047879 prefixEnd_5047879 := by exact prefixLift 5047879
  have htrace : WordTrace (prefixWord ++ tailWord_5047879) baseStart_5047879 baseEnd_5047879 := by
    simpa [prefixWord, tailWord_5047879, baseEnd_5047879] using wordTrace_append hprefix tailTrace_5047879
  have hstable : (prefixWord ++ tailWord_5047879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047879).length < 2 ^ (prefixWord ++ tailWord_5047879).sum := by decide
  have hdescent : baseEnd_5047879 < baseStart_5047879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047892 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5047892 : Nat := 118140960795 + 5047892 * 2 ^ 59
def prefixEnd_5047892 : Nat := 4983230072969 + 3 ^ 40 * 5047892 * 2
def baseEnd_5047892 : Nat := 2591994887985669333035173

theorem tailTrace_5047892 : CollatzResearch.WordTrace tailWord_5047892 prefixEnd_5047892 2591994887985669333035173 := by
  unfold tailWord_5047892
  simp only [CollatzResearch.WordTrace]
  refine ⟨92055873314178435081260965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122741164418904580108347953 92055873314178435081260965)
  ·
    refine ⟨17260476246408456577736431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92055873314178435081260965 17260476246408456577736431)
    ·
      refine ⟨25890714369612684866604647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17260476246408456577736431 25890714369612684866604647)
      ·
        refine ⟨38836071554419027299906971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25890714369612684866604647 38836071554419027299906971)
        ·
          refine ⟨58254107331628540949860457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38836071554419027299906971 58254107331628540949860457)
          ·
            refine ⟨43690580498721405712395343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58254107331628540949860457 43690580498721405712395343)
            ·
              refine ⟨65535870748082108568593015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43690580498721405712395343 65535870748082108568593015)
              ·
                refine ⟨98303806122123162852889523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65535870748082108568593015 98303806122123162852889523)
                ·
                  refine ⟨147455709183184744279334285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98303806122123162852889523 147455709183184744279334285)
                  ·
                    refine ⟨55295890943694279104750357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147455709183184744279334285 55295890943694279104750357)
                    ·
                      refine ⟨2591994887985669333035173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55295890943694279104750357 2591994887985669333035173)
                      ·
                        rfl

theorem cell23_5047892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5047892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047892 prefixEnd_5047892 := by exact prefixLift 5047892
  have htrace : WordTrace (prefixWord ++ tailWord_5047892) baseStart_5047892 baseEnd_5047892 := by
    simpa [prefixWord, tailWord_5047892, baseEnd_5047892] using wordTrace_append hprefix tailTrace_5047892
  have hstable : (prefixWord ++ tailWord_5047892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047892).length < 2 ^ (prefixWord ++ tailWord_5047892).sum := by decide
  have hdescent : baseEnd_5047892 < baseStart_5047892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047940 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5047940 : Nat := 118140960795 + 5047940 * 2 ^ 59
def prefixEnd_5047940 : Nat := 4983230072969 + 3 ^ 40 * 5047940 * 2
def baseEnd_5047940 : Nat := 864006511685695048411651

theorem tailTrace_5047940 : CollatzResearch.WordTrace tailWord_5047940 prefixEnd_5047940 864006511685695048411651 := by
  unfold tailWord_5047940
  simp only [CollatzResearch.WordTrace]
  refine ⟨92056748666091487180134637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122742331554788649573512849 92056748666091487180134637)
  ·
    refine ⟨34521280749784307692550489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92056748666091487180134637 34521280749784307692550489)
    ·
      refine ⟨25890960562338230769412867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34521280749784307692550489 25890960562338230769412867)
      ·
        refine ⟨38836440843507346154119301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25890960562338230769412867 38836440843507346154119301)
        ·
          refine ⟨7281832658157627403897369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38836440843507346154119301 7281832658157627403897369)
          ·
            refine ⟨5461374493618220552923027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7281832658157627403897369 5461374493618220552923027)
            ·
              refine ⟨8192061740427330829384541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461374493618220552923027 8192061740427330829384541)
              ·
                refine ⟨3072023152660249061019203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8192061740427330829384541 3072023152660249061019203)
                ·
                  refine ⟨4608034728990373591528805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072023152660249061019203 4608034728990373591528805)
                  ·
                    refine ⟨864006511685695048411651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4608034728990373591528805 864006511685695048411651)
                    ·
                      rfl

theorem cell23_5047940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5047940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047940 prefixEnd_5047940 := by exact prefixLift 5047940
  have htrace : WordTrace (prefixWord ++ tailWord_5047940) baseStart_5047940 baseEnd_5047940 := by
    simpa [prefixWord, tailWord_5047940, baseEnd_5047940] using wordTrace_append hprefix tailTrace_5047940
  have hstable : (prefixWord ++ tailWord_5047940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047940).length < 2 ^ (prefixWord ++ tailWord_5047940).sum := by decide
  have hdescent : baseEnd_5047940 < baseStart_5047940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047970 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_5047970 : Nat := 118140960795 + 5047970 * 2 ^ 59
def prefixEnd_5047970 : Nat := 4983230072969 + 3 ^ 40 * 5047970 * 2
def baseEnd_5047970 : Nat := 288003882164080003095535

theorem tailTrace_5047970 : CollatzResearch.WordTrace tailWord_5047970 prefixEnd_5047970 288003882164080003095535 := by
  unfold tailWord_5047970
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028647880518572370965341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122743061014716192989240909 46028647880518572370965341)
  ·
    refine ⟨17260742955194464639112003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46028647880518572370965341 17260742955194464639112003)
    ·
      refine ⟨25891114432791696958668005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17260742955194464639112003 25891114432791696958668005)
      ·
        refine ⟨4854583956148443179750251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25891114432791696958668005 4854583956148443179750251)
        ·
          refine ⟨7281875934222664769625377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854583956148443179750251 7281875934222664769625377)
          ·
            refine ⟨5461406950666998577219033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7281875934222664769625377 5461406950666998577219033)
            ·
              refine ⟨4096055213000248932914275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5461406950666998577219033 4096055213000248932914275)
              ·
                refine ⟨6144082819500373399371413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096055213000248932914275 6144082819500373399371413)
                ·
                  refine ⟨288003882164080003095535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6144082819500373399371413 288003882164080003095535)
                  ·
                    rfl

theorem cell23_5047970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_5047970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047970 prefixEnd_5047970 := by exact prefixLift 5047970
  have htrace : WordTrace (prefixWord ++ tailWord_5047970) baseStart_5047970 baseEnd_5047970 := by
    simpa [prefixWord, tailWord_5047970, baseEnd_5047970] using wordTrace_append hprefix tailTrace_5047970
  have hstable : (prefixWord ++ tailWord_5047970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047970).length < 2 ^ (prefixWord ++ tailWord_5047970).sum := by decide
  have hdescent : baseEnd_5047970 < baseStart_5047970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047986 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_5047986 : Nat := 118140960795 + 5047986 * 2 ^ 59
def prefixEnd_5047986 : Nat := 4983230072969 + 3 ^ 40 * 5047986 * 2
def baseEnd_5047986 : Nat := 2592043155167191965259741

theorem tailTrace_5047986 : CollatzResearch.WordTrace tailWord_5047986 prefixEnd_5047986 2592043155167191965259741 := by
  unfold tailWord_5047986
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028793772504081054110953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122743450060010882810962541 46028793772504081054110953)
  ·
    refine ⟨34521595329378060790583215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46028793772504081054110953 34521595329378060790583215)
    ·
      refine ⟨51782392994067091185874823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34521595329378060790583215 51782392994067091185874823)
      ·
        refine ⟨77673589491100636778812235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51782392994067091185874823 77673589491100636778812235)
        ·
          refine ⟨116510384236650955168218353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77673589491100636778812235 116510384236650955168218353)
          ·
            refine ⟨87382788177488216376163765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116510384236650955168218353 87382788177488216376163765)
            ·
              refine ⟨8192136391639520285265353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87382788177488216376163765 8192136391639520285265353)
              ·
                refine ⟨6144102293729640213949015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8192136391639520285265353 6144102293729640213949015)
                ·
                  refine ⟨9216153440594460320923523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144102293729640213949015 9216153440594460320923523)
                  ·
                    refine ⟨13824230160891690481385285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9216153440594460320923523 13824230160891690481385285)
                    ·
                      refine ⟨2592043155167191965259741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13824230160891690481385285 2592043155167191965259741)
                      ·
                        rfl

theorem cell23_5047986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_5047986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047986 prefixEnd_5047986 := by exact prefixLift 5047986
  have htrace : WordTrace (prefixWord ++ tailWord_5047986) baseStart_5047986 baseEnd_5047986 := by
    simpa [prefixWord, tailWord_5047986, baseEnd_5047986] using wordTrace_append hprefix tailTrace_5047986
  have hstable : (prefixWord ++ tailWord_5047986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047986).length < 2 ^ (prefixWord ++ tailWord_5047986).sum := by decide
  have hdescent : baseEnd_5047986 < baseStart_5047986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047990 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5047990 : Nat := 118140960795 + 5047990 * 2 ^ 59
def prefixEnd_5047990 : Nat := 4983230072969 + 3 ^ 40 * 5047990 * 2
def baseEnd_5047990 : Nat := 2592045209089809949609723

theorem tailTrace_5047990 : CollatzResearch.WordTrace tailWord_5047990 prefixEnd_5047990 2592045209089809949609723 := by
  unfold tailWord_5047990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11507207561375114556224339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122743547321334555266392949 11507207561375114556224339)
  ·
    refine ⟨17260811342062671834336509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11507207561375114556224339 17260811342062671834336509)
    ·
      refine ⟨6472804253273501937876191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17260811342062671834336509 6472804253273501937876191)
      ·
        refine ⟨9709206379910252906814287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6472804253273501937876191 9709206379910252906814287)
        ·
          refine ⟨14563809569865379360221431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9709206379910252906814287 14563809569865379360221431)
          ·
            refine ⟨21845714354798069040332147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14563809569865379360221431 21845714354798069040332147)
            ·
              refine ⟨32768571532197103560498221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21845714354798069040332147 32768571532197103560498221)
              ·
                refine ⟨12288214324573913835186833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32768571532197103560498221 12288214324573913835186833)
                ·
                  refine ⟨9216160743430435376390125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12288214324573913835186833 9216160743430435376390125)
                  ·
                    refine ⟨3456060278786413266146297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9216160743430435376390125 3456060278786413266146297)
                    ·
                      refine ⟨2592045209089809949609723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456060278786413266146297 2592045209089809949609723)
                      ·
                        rfl

theorem cell23_5047990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5047990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047990 prefixEnd_5047990 := by exact prefixLift 5047990
  have htrace : WordTrace (prefixWord ++ tailWord_5047990) baseStart_5047990 baseEnd_5047990 := by
    simpa [prefixWord, tailWord_5047990, baseEnd_5047990] using wordTrace_append hprefix tailTrace_5047990
  have hstable : (prefixWord ++ tailWord_5047990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047990).length < 2 ^ (prefixWord ++ tailWord_5047990).sum := by decide
  have hdescent : baseEnd_5047990 < baseStart_5047990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5047999 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_5047999 : Nat := 118140960795 + 5047999 * 2 ^ 59
def prefixEnd_5047999 : Nat := 4983230072969 + 3 ^ 40 * 5047999 * 2
def baseEnd_5047999 : Nat := 2592049830415700414397181

theorem tailTrace_5047999 : CollatzResearch.WordTrace tailWord_5047999 prefixEnd_5047999 2592049830415700414397181 := by
  unfold tailWord_5047999
  simp only [CollatzResearch.WordTrace]
  refine ⟨184115649238969227436667051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122743766159312818291111367 184115649238969227436667051)
  ·
    refine ⟨276173473858453841155000577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184115649238969227436667051 276173473858453841155000577)
    ·
      refine ⟨207130105393840380866250433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276173473858453841155000577 207130105393840380866250433)
      ·
        refine ⟨155347579045380285649687825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207130105393840380866250433 155347579045380285649687825)
        ·
          refine ⟨116510684284035214237265869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155347579045380285649687825 116510684284035214237265869)
          ·
            refine ⟨43691506606513205338974701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116510684284035214237265869 43691506606513205338974701)
            ·
              refine ⟨16384314977442452002115513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43691506606513205338974701 16384314977442452002115513)
              ·
                refine ⟨12288236233081839001586635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16384314977442452002115513 12288236233081839001586635)
                ·
                  refine ⟨18432354349622758502379953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12288236233081839001586635 18432354349622758502379953)
                  ·
                    refine ⟨13824265762217068876784965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18432354349622758502379953 13824265762217068876784965)
                    ·
                      refine ⟨2592049830415700414397181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13824265762217068876784965 2592049830415700414397181)
                      ·
                        rfl

theorem cell23_5047999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_5047999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5047999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5047999 prefixEnd_5047999 := by exact prefixLift 5047999
  have htrace : WordTrace (prefixWord ++ tailWord_5047999) baseStart_5047999 baseEnd_5047999 := by
    simpa [prefixWord, tailWord_5047999, baseEnd_5047999] using wordTrace_append hprefix tailTrace_5047999
  have hstable : (prefixWord ++ tailWord_5047999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5047999).length < 2 ^ (prefixWord ++ tailWord_5047999).sum := by decide
  have hdescent : baseEnd_5047999 < baseStart_5047999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5047999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048036 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_5048036 : Nat := 118140960795 + 5048036 * 2 ^ 59
def prefixEnd_5048036 : Nat := 4983230072969 + 3 ^ 40 * 5048036 * 2
def baseEnd_5048036 : Nat := 2592068829199916769634511

theorem tailTrace_5048036 : CollatzResearch.WordTrace tailWord_5048036 prefixEnd_5048036 2592068829199916769634511 := by
  unfold tailWord_5048036
  simp only [CollatzResearch.WordTrace]
  refine ⟨92058499369917591377881981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122744665826556788503842641 92058499369917591377881981)
  ·
    refine ⟨34521937263719096766705743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92058499369917591377881981 34521937263719096766705743)
    ·
      refine ⟨51782905895578645150058615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34521937263719096766705743 51782905895578645150058615)
      ·
        refine ⟨77674358843367967725087923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51782905895578645150058615 77674358843367967725087923)
        ·
          refine ⟨116511538265051951587631885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77674358843367967725087923 116511538265051951587631885)
          ·
            refine ⟨43691826849394481845361957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116511538265051951587631885 43691826849394481845361957)
            ·
              refine ⟨8192217534261465346005367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43691826849394481845361957 8192217534261465346005367)
              ·
                refine ⟨12288326301392198019008051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192217534261465346005367 12288326301392198019008051)
                ·
                  refine ⟨18432489452088297028512077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12288326301392198019008051 18432489452088297028512077)
                  ·
                    refine ⟨6912183544533111385692029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18432489452088297028512077 6912183544533111385692029)
                    ·
                      refine ⟨2592068829199916769634511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912183544533111385692029 2592068829199916769634511)
                      ·
                        rfl

theorem cell23_5048036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_5048036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048036 prefixEnd_5048036 := by exact prefixLift 5048036
  have htrace : WordTrace (prefixWord ++ tailWord_5048036) baseStart_5048036 baseEnd_5048036 := by
    simpa [prefixWord, tailWord_5048036, baseEnd_5048036] using wordTrace_append hprefix tailTrace_5048036
  have hstable : (prefixWord ++ tailWord_5048036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048036).length < 2 ^ (prefixWord ++ tailWord_5048036).sum := by decide
  have hdescent : baseEnd_5048036 < baseStart_5048036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048076 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_5048076 : Nat := 118140960795 + 5048076 * 2 ^ 59
def prefixEnd_5048076 : Nat := 4983230072969 + 3 ^ 40 * 5048076 * 2
def baseEnd_5048076 : Nat := 2592089368426096613134327

theorem tailTrace_5048076 : CollatzResearch.WordTrace tailWord_5048076 prefixEnd_5048076 2592089368426096613134327 := by
  unfold tailWord_5048076
  simp only [CollatzResearch.WordTrace]
  refine ⟨92059228829845134793610041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122745638439793513058146721 92059228829845134793610041)
  ·
    refine ⟨69044421622383851095207531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92059228829845134793610041 69044421622383851095207531)
    ·
      refine ⟨103566632433575776642811297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69044421622383851095207531 103566632433575776642811297)
      ·
        refine ⟨77674974325181832482108473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103566632433575776642811297 77674974325181832482108473)
        ·
          refine ⟨58256230743886374361581355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77674974325181832482108473 58256230743886374361581355)
          ·
            refine ⟨87384346115829561542372033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58256230743886374361581355 87384346115829561542372033)
            ·
              refine ⟨65538259586872171156779025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87384346115829561542372033 65538259586872171156779025)
              ·
                refine ⟨49153694690154128367584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65538259586872171156779025 49153694690154128367584269)
                ·
                  refine ⟨18432635508807798137844101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49153694690154128367584269 18432635508807798137844101)
                  ·
                    refine ⟨3456119157901462150845769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18432635508807798137844101 3456119157901462150845769)
                    ·
                      refine ⟨2592089368426096613134327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456119157901462150845769 2592089368426096613134327)
                      ·
                        rfl

theorem cell23_5048076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_5048076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048076 prefixEnd_5048076 := by exact prefixLift 5048076
  have htrace : WordTrace (prefixWord ++ tailWord_5048076) baseStart_5048076 baseEnd_5048076 := by
    simpa [prefixWord, tailWord_5048076, baseEnd_5048076] using wordTrace_append hprefix tailTrace_5048076
  have hstable : (prefixWord ++ tailWord_5048076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048076).length < 2 ^ (prefixWord ++ tailWord_5048076).sum := by decide
  have hdescent : baseEnd_5048076 < baseStart_5048076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048079 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_5048079 : Nat := 118140960795 + 5048079 * 2 ^ 59
def prefixEnd_5048079 : Nat := 4983230072969 + 3 ^ 40 * 5048079 * 2
def baseEnd_5048079 : Nat := 2592090908868060101396813

theorem tailTrace_5048079 : CollatzResearch.WordTrace tailWord_5048079 prefixEnd_5048079 2592090908868060101396813 := by
  unfold tailWord_5048079
  simp only [CollatzResearch.WordTrace]
  refine ⟨184118567078679401099579291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122745711385786267399719527 184118567078679401099579291)
  ·
    refine ⟨276177850618019101649368937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184118567078679401099579291 276177850618019101649368937)
    ·
      refine ⟨207133387963514326237026703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276177850618019101649368937 207133387963514326237026703)
      ·
        refine ⟨310700081945271489355540055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207133387963514326237026703 310700081945271489355540055)
        ·
          refine ⟨466050122917907234033310083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310700081945271489355540055 466050122917907234033310083)
          ·
            refine ⟨699075184376860851049965125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466050122917907234033310083 699075184376860851049965125)
            ·
              refine ⟨131076597070661409571868461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 699075184376860851049965125 131076597070661409571868461)
              ·
                refine ⟨49153723901498028589450673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131076597070661409571868461 49153723901498028589450673)
                ·
                  refine ⟨36865292926123521442088005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49153723901498028589450673 36865292926123521442088005)
                  ·
                    refine ⟨6912242423648160270391501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36865292926123521442088005 6912242423648160270391501)
                    ·
                      refine ⟨2592090908868060101396813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912242423648160270391501 2592090908868060101396813)
                      ·
                        rfl

theorem cell23_5048079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_5048079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048079 prefixEnd_5048079 := by exact prefixLift 5048079
  have htrace : WordTrace (prefixWord ++ tailWord_5048079) baseStart_5048079 baseEnd_5048079 := by
    simpa [prefixWord, tailWord_5048079, baseEnd_5048079] using wordTrace_append hprefix tailTrace_5048079
  have hstable : (prefixWord ++ tailWord_5048079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048079).length < 2 ^ (prefixWord ++ tailWord_5048079).sum := by decide
  have hdescent : baseEnd_5048079 < baseStart_5048079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048084 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5048084 : Nat := 118140960795 + 5048084 * 2 ^ 59
def prefixEnd_5048084 : Nat := 4983230072969 + 3 ^ 40 * 5048084 * 2
def baseEnd_5048084 : Nat := 2592093476271332581834291

theorem tailTrace_5048084 : CollatzResearch.WordTrace tailWord_5048084 prefixEnd_5048084 2592093476271332581834291 := by
  unfold tailWord_5048084
  simp only [CollatzResearch.WordTrace]
  refine ⟨92059374721830643476755653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122745832962440857969007537 92059374721830643476755653)
  ·
    refine ⟨17261132760343245651891685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92059374721830643476755653 17261132760343245651891685)
    ·
      refine ⟨3236462392564358559729691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17261132760343245651891685 3236462392564358559729691)
      ·
        refine ⟨4854693588846537839594537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236462392564358559729691 4854693588846537839594537)
        ·
          refine ⟨3641020191634903379695903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4854693588846537839594537 3641020191634903379695903)
          ·
            refine ⟨5461530287452355069543855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641020191634903379695903 5461530287452355069543855)
            ·
              refine ⟨8192295431178532604315783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461530287452355069543855 8192295431178532604315783)
              ·
                refine ⟨12288443146767798906473675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192295431178532604315783 12288443146767798906473675)
                ·
                  refine ⟨18432664720151698359710513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12288443146767798906473675 18432664720151698359710513)
                  ·
                    refine ⟨13824498540113773769782885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18432664720151698359710513 13824498540113773769782885)
                    ·
                      refine ⟨2592093476271332581834291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13824498540113773769782885 2592093476271332581834291)
                      ·
                        rfl

theorem cell23_5048084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5048084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048084 prefixEnd_5048084 := by exact prefixLift 5048084
  have htrace : WordTrace (prefixWord ++ tailWord_5048084) baseStart_5048084 baseEnd_5048084 := by
    simpa [prefixWord, tailWord_5048084, baseEnd_5048084] using wordTrace_append hprefix tailTrace_5048084
  have hstable : (prefixWord ++ tailWord_5048084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048084).length < 2 ^ (prefixWord ++ tailWord_5048084).sum := by decide
  have hdescent : baseEnd_5048084 < baseStart_5048084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048099 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 7]
def baseStart_5048099 : Nat := 118140960795 + 5048099 * 2 ^ 59
def prefixEnd_5048099 : Nat := 4983230072969 + 3 ^ 40 * 5048099 * 2
def baseEnd_5048099 : Nat := 288011242053461113682969

theorem tailTrace_5048099 : CollatzResearch.WordTrace tailWord_5048099 prefixEnd_5048099 288011242053461113682969 := by
  unfold tailWord_5048099
  simp only [CollatzResearch.WordTrace]
  refine ⟨184119296538606944515307351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122746197692404629676871567 184119296538606944515307351)
  ·
    refine ⟨276178944807910416772961027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184119296538606944515307351 276178944807910416772961027)
    ·
      refine ⟨414268417211865625159441541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276178944807910416772961027 414268417211865625159441541)
      ·
        refine ⟨77675328227224804717395289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 414268417211865625159441541 77675328227224804717395289)
        ·
          refine ⟨58256496170418603538046467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77675328227224804717395289 58256496170418603538046467)
          ·
            refine ⟨87384744255627905307069701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58256496170418603538046467 87384744255627905307069701)
            ·
              refine ⟨16384639547930232245075569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87384744255627905307069701 16384639547930232245075569)
              ·
                refine ⟨12288479660947674183806677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16384639547930232245075569 12288479660947674183806677)
                ·
                  refine ⟨288011242053461113682969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12288479660947674183806677 288011242053461113682969)
                  ·
                    rfl

theorem cell23_5048099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 7].length) (baseStart_5048099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048099 prefixEnd_5048099 := by exact prefixLift 5048099
  have htrace : WordTrace (prefixWord ++ tailWord_5048099) baseStart_5048099 baseEnd_5048099 := by
    simpa [prefixWord, tailWord_5048099, baseEnd_5048099] using wordTrace_append hprefix tailTrace_5048099
  have hstable : (prefixWord ++ tailWord_5048099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048099).length < 2 ^ (prefixWord ++ tailWord_5048099).sum := by decide
  have hdescent : baseEnd_5048099 < baseStart_5048099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048133 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 5]
def baseStart_5048133 : Nat := 118140960795 + 5048133 * 2 ^ 59
def prefixEnd_5048133 : Nat := 4983230072969 + 3 ^ 40 * 5048133 * 2
def baseEnd_5048133 : Nat := 288013181869266987791285

theorem tailTrace_5048133 : CollatzResearch.WordTrace tailWord_5048133 prefixEnd_5048133 288013181869266987791285 := by
  unfold tailWord_5048133
  simp only [CollatzResearch.WordTrace]
  refine ⟨184120536620483768322045053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122747024413655845548030035 184120536620483768322045053)
  ·
    refine ⟨69045201232681413120766895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184120536620483768322045053 69045201232681413120766895)
    ·
      refine ⟨103567801849022119681150343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69045201232681413120766895 103567801849022119681150343)
      ·
        refine ⟨155351702773533179521725515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103567801849022119681150343 155351702773533179521725515)
        ·
          refine ⟨233027554160299769282588273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155351702773533179521725515 233027554160299769282588273)
          ·
            refine ⟨174770665620224826961941205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233027554160299769282588273 174770665620224826961941205)
            ·
              refine ⟨4096187475474019381920497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 174770665620224826961941205 4096187475474019381920497)
              ·
                refine ⟨3072140606605514536440373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096187475474019381920497 3072140606605514536440373)
                ·
                  refine ⟨288013181869266987791285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3072140606605514536440373 288013181869266987791285)
                  ·
                    rfl

theorem cell23_5048133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_5048133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048133 prefixEnd_5048133 := by exact prefixLift 5048133
  have htrace : WordTrace (prefixWord ++ tailWord_5048133) baseStart_5048133 baseEnd_5048133 := by
    simpa [prefixWord, tailWord_5048133, baseEnd_5048133] using wordTrace_append hprefix tailTrace_5048133
  have hstable : (prefixWord ++ tailWord_5048133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048133).length < 2 ^ (prefixWord ++ tailWord_5048133).sum := by decide
  have hdescent : baseEnd_5048133 < baseStart_5048133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048163 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 2, 5]
def baseStart_5048163 : Nat := 118140960795 + 5048163 * 2 ^ 59
def prefixEnd_5048163 : Nat := 4983230072969 + 3 ^ 40 * 5048163 * 2
def baseEnd_5048163 : Nat := 864044680414345924248809

theorem tailTrace_5048163 : CollatzResearch.WordTrace tailWord_5048163 prefixEnd_5048163 864044680414345924248809 := by
  unfold tailWord_5048163
  simp only [CollatzResearch.WordTrace]
  refine ⟨184121630810375083445637143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122747753873583388963758095 184121630810375083445637143)
  ·
    refine ⟨276182446215562625168455715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184121630810375083445637143 276182446215562625168455715)
    ·
      refine ⟨414273669323343937752683573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276182446215562625168455715 414273669323343937752683573)
      ·
        refine ⟨38838156499063494164314085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 414273669323343937752683573 38838156499063494164314085)
        ·
          refine ⟨7282154343574405155808891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38838156499063494164314085 7282154343574405155808891)
          ·
            refine ⟨10923231515361607733713337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282154343574405155808891 10923231515361607733713337)
            ·
              refine ⟨8192423636521205800285003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10923231515361607733713337 8192423636521205800285003)
              ·
                refine ⟨12288635454781808700427505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192423636521205800285003 12288635454781808700427505)
                ·
                  refine ⟨9216476591086356525320629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12288635454781808700427505 9216476591086356525320629)
                  ·
                    refine ⟨864044680414345924248809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9216476591086356525320629 864044680414345924248809)
                    ·
                      rfl

theorem cell23_5048163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 5].length) (baseStart_5048163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048163 prefixEnd_5048163 := by exact prefixLift 5048163
  have htrace : WordTrace (prefixWord ++ tailWord_5048163) baseStart_5048163 baseEnd_5048163 := by
    simpa [prefixWord, tailWord_5048163, baseEnd_5048163] using wordTrace_append hprefix tailTrace_5048163
  have hstable : (prefixWord ++ tailWord_5048163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048163).length < 2 ^ (prefixWord ++ tailWord_5048163).sum := by decide
  have hdescent : baseEnd_5048163 < baseStart_5048163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048179 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_5048179 : Nat := 118140960795 + 5048179 * 2 ^ 59
def prefixEnd_5048179 : Nat := 4983230072969 + 3 ^ 40 * 5048179 * 2
def baseEnd_5048179 : Nat := 2592142256933509710146353

theorem tailTrace_5048179 : CollatzResearch.WordTrace tailWord_5048179 prefixEnd_5048179 2592142256933509710146353 := by
  unfold tailWord_5048179
  simp only [CollatzResearch.WordTrace]
  refine ⟨184122214378317118178219591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122748142918878078785479727 184122214378317118178219591)
  ·
    refine ⟨276183321567475677267329387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184122214378317118178219591 276183321567475677267329387)
    ·
      refine ⟨414274982351213515900994081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276183321567475677267329387 414274982351213515900994081)
      ·
        refine ⟨310706236763410136925745561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414274982351213515900994081 310706236763410136925745561)
        ·
          refine ⟨233029677572557602694309171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310706236763410136925745561 233029677572557602694309171)
          ·
            refine ⟨349544516358836404041463757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233029677572557602694309171 349544516358836404041463757)
            ·
              refine ⟨131079193634563651515548909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349544516358836404041463757 131079193634563651515548909)
              ·
                refine ⟨49154697612961369318330841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131079193634563651515548909 49154697612961369318330841)
                ·
                  refine ⟨36866023209721026988748131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49154697612961369318330841 36866023209721026988748131)
                  ·
                    refine ⟨55299034814581540483122197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36866023209721026988748131 55299034814581540483122197)
                    ·
                      refine ⟨2592142256933509710146353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55299034814581540483122197 2592142256933509710146353)
                      ·
                        rfl

theorem cell23_5048179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_5048179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048179 prefixEnd_5048179 := by exact prefixLift 5048179
  have htrace : WordTrace (prefixWord ++ tailWord_5048179) baseStart_5048179 baseEnd_5048179 := by
    simpa [prefixWord, tailWord_5048179, baseEnd_5048179] using wordTrace_append hprefix tailTrace_5048179
  have hstable : (prefixWord ++ tailWord_5048179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048179).length < 2 ^ (prefixWord ++ tailWord_5048179).sum := by decide
  have hdescent : baseEnd_5048179 < baseStart_5048179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048200 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_5048200 : Nat := 118140960795 + 5048200 * 2 ^ 59
def prefixEnd_5048200 : Nat := 4983230072969 + 3 ^ 40 * 5048200 * 2
def baseEnd_5048200 : Nat := 2592153040027254127983757

theorem tailTrace_5048200 : CollatzResearch.WordTrace tailWord_5048200 prefixEnd_5048200 2592153040027254127983757 := by
  unfold tailWord_5048200
  simp only [CollatzResearch.WordTrace]
  refine ⟨92061490155620519382367027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122748653540827359176489369 92061490155620519382367027)
  ·
    refine ⟨138092235233430779073550541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92061490155620519382367027 138092235233430779073550541)
    ·
      refine ⟨51784588212536542152581453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138092235233430779073550541 51784588212536542152581453)
      ·
        refine ⟨19419220579701203307218045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51784588212536542152581453 19419220579701203307218045)
        ·
          refine ⟨7282207717387951240206767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19419220579701203307218045 7282207717387951240206767)
          ·
            refine ⟨10923311576081926860310151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282207717387951240206767 10923311576081926860310151)
            ·
              refine ⟨16384967364122890290465227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10923311576081926860310151 16384967364122890290465227)
              ·
                refine ⟨24577451046184335435697841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16384967364122890290465227 24577451046184335435697841)
                ·
                  refine ⟨18433088284638251576773381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24577451046184335435697841 18433088284638251576773381)
                  ·
                    refine ⟨3456204053369672170645009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18433088284638251576773381 3456204053369672170645009)
                    ·
                      refine ⟨2592153040027254127983757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456204053369672170645009 2592153040027254127983757)
                      ·
                        rfl

theorem cell23_5048200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_5048200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048200 prefixEnd_5048200 := by exact prefixLift 5048200
  have htrace : WordTrace (prefixWord ++ tailWord_5048200) baseStart_5048200 baseEnd_5048200 := by
    simpa [prefixWord, tailWord_5048200, baseEnd_5048200] using wordTrace_append hprefix tailTrace_5048200
  have hstable : (prefixWord ++ tailWord_5048200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048200).length < 2 ^ (prefixWord ++ tailWord_5048200).sum := by decide
  have hdescent : baseEnd_5048200 < baseStart_5048200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048210 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_5048210 : Nat := 118140960795 + 5048210 * 2 ^ 59
def prefixEnd_5048210 : Nat := 4983230072969 + 3 ^ 40 * 5048210 * 2
def baseEnd_5048210 : Nat := 864052724944599696286237

theorem tailTrace_5048210 : CollatzResearch.WordTrace tailWord_5048210 prefixEnd_5048210 864052724944599696286237 := by
  unfold tailWord_5048210
  simp only [CollatzResearch.WordTrace]
  refine ⟨46030836260301202618149521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122748896694136540315065389 46030836260301202618149521)
  ·
    refine ⟨34523127195225901963612141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46030836260301202618149521 34523127195225901963612141)
    ·
      refine ⟨12946172698209713236354553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34523127195225901963612141 12946172698209713236354553)
      ·
        refine ⟨9709629523657284927265915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12946172698209713236354553 9709629523657284927265915)
        ·
          refine ⟨14564444285485927390898873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9709629523657284927265915 14564444285485927390898873)
          ·
            refine ⟨10923333214114445543174155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14564444285485927390898873 10923333214114445543174155)
            ·
              refine ⟨16384999821171668314761233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10923333214114445543174155 16384999821171668314761233)
              ·
                refine ⟨12288749865878751236070925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16384999821171668314761233 12288749865878751236070925)
                ·
                  refine ⟨4608281199704531713526597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12288749865878751236070925 4608281199704531713526597)
                  ·
                    refine ⟨864052724944599696286237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4608281199704531713526597 864052724944599696286237)
                    ·
                      rfl

theorem cell23_5048210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_5048210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048210 prefixEnd_5048210 := by exact prefixLift 5048210
  have htrace : WordTrace (prefixWord ++ tailWord_5048210) baseStart_5048210 baseEnd_5048210 := by
    simpa [prefixWord, tailWord_5048210, baseEnd_5048210] using wordTrace_append hprefix tailTrace_5048210
  have hstable : (prefixWord ++ tailWord_5048210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048210).length < 2 ^ (prefixWord ++ tailWord_5048210).sum := by decide
  have hdescent : baseEnd_5048210 < baseStart_5048210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048214 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5048214 : Nat := 118140960795 + 5048214 * 2 ^ 59
def prefixEnd_5048214 : Nat := 4983230072969 + 3 ^ 40 * 5048214 * 2
def baseEnd_5048214 : Nat := 864053409585472357736231

theorem tailTrace_5048214 : CollatzResearch.WordTrace tailWord_5048214 prefixEnd_5048214 864053409585472357736231 := by
  unfold tailWord_5048214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11507718183324394947233981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122748993955460212770495797 11507718183324394947233981)
  ·
    refine ⟨4315394318746648105212743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11507718183324394947233981 4315394318746648105212743)
    ·
      refine ⟨6473091478119972157819115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315394318746648105212743 6473091478119972157819115)
      ·
        refine ⟨9709637217179958236728673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6473091478119972157819115 9709637217179958236728673)
        ·
          refine ⟨7282227912884968677546505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9709637217179958236728673 7282227912884968677546505)
          ·
            refine ⟨5461670934663726508159879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7282227912884968677546505 5461670934663726508159879)
            ·
              refine ⟨8192506401995589762239819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461670934663726508159879 8192506401995589762239819)
              ·
                refine ⟨12288759602993384643359729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192506401995589762239819 12288759602993384643359729)
                ·
                  refine ⟨9216569702245038482519797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12288759602993384643359729 9216569702245038482519797)
                  ·
                    refine ⟨864053409585472357736231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9216569702245038482519797 864053409585472357736231)
                    ·
                      rfl

theorem cell23_5048214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5048214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048214 prefixEnd_5048214 := by exact prefixLift 5048214
  have htrace : WordTrace (prefixWord ++ tailWord_5048214) baseStart_5048214 baseEnd_5048214 := by
    simpa [prefixWord, tailWord_5048214, baseEnd_5048214] using wordTrace_append hprefix tailTrace_5048214
  have hstable : (prefixWord ++ tailWord_5048214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048214).length < 2 ^ (prefixWord ++ tailWord_5048214).sum := by decide
  have hdescent : baseEnd_5048214 < baseStart_5048214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048220 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5048220 : Nat := 118140960795 + 5048220 * 2 ^ 59
def prefixEnd_5048220 : Nat := 4983230072969 + 3 ^ 40 * 5048220 * 2
def baseEnd_5048220 : Nat := 2592163309640344049733665

theorem tailTrace_5048220 : CollatzResearch.WordTrace tailWord_5048220 prefixEnd_5048220 2592163309640344049733665 := by
  unfold tailWord_5048220
  simp only [CollatzResearch.WordTrace]
  refine ⟨92061854885584291090231057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122749139847445721453641409 92061854885584291090231057)
  ·
    refine ⟨69046391164188218317673293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92061854885584291090231057 69046391164188218317673293)
    ·
      refine ⟨25892396686570581869127485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69046391164188218317673293 25892396686570581869127485)
      ·
        refine ⟨9709648757463968200922807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25892396686570581869127485 9709648757463968200922807)
        ·
          refine ⟨14564473136195952301384211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9709648757463968200922807 14564473136195952301384211)
          ·
            refine ⟨21846709704293928452076317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14564473136195952301384211 21846709704293928452076317)
            ·
              refine ⟨8192516139110223169528619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21846709704293928452076317 8192516139110223169528619)
              ·
                refine ⟨12288774208665334754292929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192516139110223169528619 12288774208665334754292929)
                ·
                  refine ⟨9216580656499001065719697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12288774208665334754292929 9216580656499001065719697)
                  ·
                    refine ⟨6912435492374250799289773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9216580656499001065719697 6912435492374250799289773)
                    ·
                      refine ⟨2592163309640344049733665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912435492374250799289773 2592163309640344049733665)
                      ·
                        rfl

theorem cell23_5048220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5048220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048220 prefixEnd_5048220 := by exact prefixLift 5048220
  have htrace : WordTrace (prefixWord ++ tailWord_5048220) baseStart_5048220 baseEnd_5048220 := by
    simpa [prefixWord, tailWord_5048220, baseEnd_5048220] using wordTrace_append hprefix tailTrace_5048220
  have hstable : (prefixWord ++ tailWord_5048220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048220).length < 2 ^ (prefixWord ++ tailWord_5048220).sum := by decide
  have hdescent : baseEnd_5048220 < baseStart_5048220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048243 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 4, 3, 2]
def baseStart_5048243 : Nat := 118140960795 + 5048243 * 2 ^ 59
def prefixEnd_5048243 : Nat := 4983230072969 + 3 ^ 40 * 5048243 * 2
def baseEnd_5048243 : Nat := 2592175119695397459746059

theorem tailTrace_5048243 : CollatzResearch.WordTrace tailWord_5048243 prefixEnd_5048243 2592175119695397459746059 := by
  unfold tailWord_5048243
  simp only [CollatzResearch.WordTrace]
  refine ⟨184124548650085257108549383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122749699100056838072366255 184124548650085257108549383)
  ·
    refine ⟨276186822975127885662824075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184124548650085257108549383 276186822975127885662824075)
    ·
      refine ⟨414280234462691828494236113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276186822975127885662824075 414280234462691828494236113)
      ·
        refine ⟨310710175847018871370677085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414280234462691828494236113 310710175847018871370677085)
        ·
          refine ⟨116516315942632076764003907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310710175847018871370677085 116516315942632076764003907)
          ·
            refine ⟨174774473913948115146005861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116516315942632076764003907 174774473913948115146005861)
            ·
              refine ⟨32770213858865271589876099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174774473913948115146005861 32770213858865271589876099)
              ·
                refine ⟨49155320788297907384814149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32770213858865271589876099 49155320788297907384814149)
                ·
                  refine ⟨9216622647805857634652653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49155320788297907384814149 9216622647805857634652653)
                  ·
                    refine ⟨3456233492927196612994745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9216622647805857634652653 3456233492927196612994745)
                    ·
                      refine ⟨2592175119695397459746059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3456233492927196612994745 2592175119695397459746059)
                      ·
                        rfl

theorem cell23_5048243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3, 2].length) (baseStart_5048243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048243 prefixEnd_5048243 := by exact prefixLift 5048243
  have htrace : WordTrace (prefixWord ++ tailWord_5048243) baseStart_5048243 baseEnd_5048243 := by
    simpa [prefixWord, tailWord_5048243, baseEnd_5048243] using wordTrace_append hprefix tailTrace_5048243
  have hstable : (prefixWord ++ tailWord_5048243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048243).length < 2 ^ (prefixWord ++ tailWord_5048243).sum := by decide
  have hdescent : baseEnd_5048243 < baseStart_5048243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5048301 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5048301 : Nat := 118140960795 + 5048301 * 2 ^ 59
def prefixEnd_5048301 : Nat := 4983230072969 + 3 ^ 40 * 5048301 * 2
def baseEnd_5048301 : Nat := 2592204901573358232820793

theorem tailTrace_5048301 : CollatzResearch.WordTrace tailWord_5048301 prefixEnd_5048301 2592204901573358232820793 := by
  unfold tailWord_5048301
  simp only [CollatzResearch.WordTrace]
  refine ⟨184126664083875133014160757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122751109389250088676107171 184126664083875133014160757)
  ·
    refine ⟨17261874757863293720077571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184126664083875133014160757 17261874757863293720077571)
    ·
      refine ⟨25892812136794940580116357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17261874757863293720077571 25892812136794940580116357)
      ·
        refine ⟨4854902275649051358771817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25892812136794940580116357 4854902275649051358771817)
        ·
          refine ⟨3641176706736788519078863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4854902275649051358771817 3641176706736788519078863)
          ·
            refine ⟨5461765060105182778618295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641176706736788519078863 5461765060105182778618295)
            ·
              refine ⟨8192647590157774167927443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461765060105182778618295 8192647590157774167927443)
              ·
                refine ⟨12288971385236661251891165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192647590157774167927443 12288971385236661251891165)
                ·
                  refine ⟨4608364269463747969459187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12288971385236661251891165 4608364269463747969459187)
                  ·
                    refine ⟨6912546404195621954188781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608364269463747969459187 6912546404195621954188781)
                    ·
                      refine ⟨2592204901573358232820793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6912546404195621954188781 2592204901573358232820793)
                      ·
                        rfl

theorem cell23_5048301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5048301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5048301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5048301 prefixEnd_5048301 := by exact prefixLift 5048301
  have htrace : WordTrace (prefixWord ++ tailWord_5048301) baseStart_5048301 baseEnd_5048301 := by
    simpa [prefixWord, tailWord_5048301, baseEnd_5048301] using wordTrace_append hprefix tailTrace_5048301
  have hstable : (prefixWord ++ tailWord_5048301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5048301).length < 2 ^ (prefixWord ++ tailWord_5048301).sum := by decide
  have hdescent : baseEnd_5048301 < baseStart_5048301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5048301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
