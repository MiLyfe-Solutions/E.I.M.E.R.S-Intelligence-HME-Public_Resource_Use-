import V185TrunkScan23Chunk1400

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8299148 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_8299148 : Nat := 118140960795 + 8299148 * 2 ^ 59
def prefixEnd_8299148 : Nat := 4983230072969 + 3 ^ 40 * 8299148 * 2
def baseEnd_8299148 : Nat := 4261451946800000778982919

theorem tailTrace_8299148 : CollatzResearch.WordTrace tailWord_8299148 prefixEnd_8299148 4261451946800000778982919 := by
  unfold tailWord_8299148
  simp only [CollatzResearch.WordTrace]
  refine ⟨151347397468805826239997049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201796529958407768319996065 151347397468805826239997049)
  ·
    refine ⟨113510548101604369679997787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151347397468805826239997049 113510548101604369679997787)
    ·
      refine ⟨170265822152406554519996681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113510548101604369679997787 170265822152406554519996681)
      ·
        refine ⟨127699366614304915889997511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170265822152406554519996681 127699366614304915889997511)
        ·
          refine ⟨191549049921457373834996267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127699366614304915889997511 191549049921457373834996267)
          ·
            refine ⟨287323574882186060752494401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191549049921457373834996267 287323574882186060752494401)
            ·
              refine ⟨215492681161639545564370801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287323574882186060752494401 215492681161639545564370801)
              ·
                refine ⟨161619510871229659173278101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215492681161639545564370801 161619510871229659173278101)
                ·
                  refine ⟨7575914572088890273747411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161619510871229659173278101 7575914572088890273747411)
                  ·
                    refine ⟨11363871858133335410621117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575914572088890273747411 11363871858133335410621117)
                    ·
                      refine ⟨4261451946800000778982919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11363871858133335410621117 4261451946800000778982919)
                      ·
                        rfl

theorem cell23_8299148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_8299148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299148 prefixEnd_8299148 := by exact prefixLift 8299148
  have htrace : WordTrace (prefixWord ++ tailWord_8299148) baseStart_8299148 baseEnd_8299148 := by
    simpa [prefixWord, tailWord_8299148, baseEnd_8299148] using wordTrace_append hprefix tailTrace_8299148
  have hstable : (prefixWord ++ tailWord_8299148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299148).length < 2 ^ (prefixWord ++ tailWord_8299148).sum := by decide
  have hdescent : baseEnd_8299148 < baseStart_8299148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299198 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_8299198 : Nat := 118140960795 + 8299198 * 2 ^ 59
def prefixEnd_8299198 : Nat := 4983230072969 + 3 ^ 40 * 8299198 * 2
def baseEnd_8299198 : Nat := 1420492540277575194452563

theorem tailTrace_8299198 : CollatzResearch.WordTrace tailWord_8299198 prefixEnd_8299198 1420492540277575194452563 := by
  unfold tailWord_8299198
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837077323428813877414281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201797745724953674012876165 37837077323428813877414281)
  ·
    refine ⟨28377807992571610408060711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37837077323428813877414281 28377807992571610408060711)
    ·
      refine ⟨42566711988857415612091067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28377807992571610408060711 42566711988857415612091067)
      ·
        refine ⟨63850067983286123418136601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42566711988857415612091067 63850067983286123418136601)
        ·
          refine ⟨47887550987464592563602451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63850067983286123418136601 47887550987464592563602451)
          ·
            refine ⟨71831326481196888845403677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47887550987464592563602451 71831326481196888845403677)
            ·
              refine ⟨26936747430448833317026379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71831326481196888845403677 26936747430448833317026379)
              ·
                refine ⟨40405121145673249975539569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26936747430448833317026379 40405121145673249975539569)
                ·
                  refine ⟨30303840859254937481654677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40405121145673249975539569 30303840859254937481654677)
                  ·
                    refine ⟨1420492540277575194452563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30303840859254937481654677 1420492540277575194452563)
                    ·
                      rfl

theorem cell23_8299198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_8299198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299198 prefixEnd_8299198 := by exact prefixLift 8299198
  have htrace : WordTrace (prefixWord ++ tailWord_8299198) baseStart_8299198 baseEnd_8299198 := by
    simpa [prefixWord, tailWord_8299198, baseEnd_8299198] using wordTrace_append hprefix tailTrace_8299198
  have hstable : (prefixWord ++ tailWord_8299198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299198).length < 2 ^ (prefixWord ++ tailWord_8299198).sum := by decide
  have hdescent : baseEnd_8299198 < baseStart_8299198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299245 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 5]
def baseStart_8299245 : Nat := 118140960795 + 8299245 * 2 ^ 59
def prefixEnd_8299245 : Nat := 4983230072969 + 3 ^ 40 * 8299245 * 2
def baseEnd_8299245 : Nat := 473500194935942988829997

theorem tailTrace_8299245 : CollatzResearch.WordTrace tailWord_8299245 prefixEnd_8299245 473500194935942988829997 := by
  unfold tailWord_8299245
  simp only [CollatzResearch.WordTrace]
  refine ⟨302698332818260238046275189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201798888545506825364183459 302698332818260238046275189)
  ·
    refine ⟨28377968701711897316838299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302698332818260238046275189 28377968701711897316838299)
    ·
      refine ⟨42566953052567845975257449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28377968701711897316838299 42566953052567845975257449)
      ·
        refine ⟨31925214789425884481443087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42566953052567845975257449 31925214789425884481443087)
        ·
          refine ⟨47887822184138826722164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31925214789425884481443087 47887822184138826722164631)
          ·
            refine ⟨71831733276208240083246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47887822184138826722164631 71831733276208240083246947)
            ·
              refine ⟨107747599914312360124870421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71831733276208240083246947 107747599914312360124870421)
              ·
                refine ⟨5050668745983391880853301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107747599914312360124870421 5050668745983391880853301)
                ·
                  refine ⟨473500194935942988829997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5050668745983391880853301 473500194935942988829997)
                  ·
                    rfl

theorem cell23_8299245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_8299245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299245 prefixEnd_8299245 := by exact prefixLift 8299245
  have htrace : WordTrace (prefixWord ++ tailWord_8299245) baseStart_8299245 baseEnd_8299245 := by
    simpa [prefixWord, tailWord_8299245, baseEnd_8299245] using wordTrace_append hprefix tailTrace_8299245
  have hstable : (prefixWord ++ tailWord_8299245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299245).length < 2 ^ (prefixWord ++ tailWord_8299245).sum := by decide
  have hdescent : baseEnd_8299245 < baseStart_8299245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299251 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_8299251 : Nat := 118140960795 + 8299251 * 2 ^ 59
def prefixEnd_8299251 : Nat := 4983230072969 + 3 ^ 40 * 8299251 * 2
def baseEnd_8299251 : Nat := 4261504835307413875994945

theorem tailTrace_8299251 : CollatzResearch.WordTrace tailWord_8299251 prefixEnd_8299251 4261504835307413875994945 := by
  unfold tailWord_8299251
  simp only [CollatzResearch.WordTrace]
  refine ⟨302698551656238501070993607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201799034437492334047329071 302698551656238501070993607)
  ·
    refine ⟨454047827484357751606490411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302698551656238501070993607 454047827484357751606490411)
    ·
      refine ⟨681071741226536627409735617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454047827484357751606490411 681071741226536627409735617)
      ·
        refine ⟨510803805919902470557301713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681071741226536627409735617 510803805919902470557301713)
        ·
          refine ⟨383102854439926852917976285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510803805919902470557301713 383102854439926852917976285)
          ·
            refine ⟨143663570414972569844241107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383102854439926852917976285 143663570414972569844241107)
            ·
              refine ⟨215495355622458854766361661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143663570414972569844241107 215495355622458854766361661)
              ·
                refine ⟨80810758358422070537385623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215495355622458854766361661 80810758358422070537385623)
                ·
                  refine ⟨121216137537633105806078435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80810758358422070537385623 121216137537633105806078435)
                  ·
                    refine ⟨181824206306449658709117653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121216137537633105806078435 181824206306449658709117653)
                    ·
                      refine ⟨4261504835307413875994945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181824206306449658709117653 4261504835307413875994945)
                      ·
                        rfl

theorem cell23_8299251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_8299251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299251 prefixEnd_8299251 := by exact prefixLift 8299251
  have htrace : WordTrace (prefixWord ++ tailWord_8299251) baseStart_8299251 baseEnd_8299251 := by
    simpa [prefixWord, tailWord_8299251, baseEnd_8299251] using wordTrace_append hprefix tailTrace_8299251
  have hstable : (prefixWord ++ tailWord_8299251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299251).length < 2 ^ (prefixWord ++ tailWord_8299251).sum := by decide
  have hdescent : baseEnd_8299251 < baseStart_8299251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299295 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_8299295 : Nat := 118140960795 + 8299295 * 2 ^ 59
def prefixEnd_8299295 : Nat := 4983230072969 + 3 ^ 40 * 8299295 * 2
def baseEnd_8299295 : Nat := 4261527428456211703844743

theorem tailTrace_8299295 : CollatzResearch.WordTrace tailWord_8299295 prefixEnd_8299295 4261527428456211703844743 := by
  unfold tailWord_8299295
  simp only [CollatzResearch.WordTrace]
  refine ⟨302700156468079096585595339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201800104312052731057063559 302700156468079096585595339)
  ·
    refine ⟨454050234702118644878393009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302700156468079096585595339 454050234702118644878393009)
    ·
      refine ⟨340537676026588983658794757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454050234702118644878393009 340537676026588983658794757)
      ·
        refine ⟨63850814254985434436024017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340537676026588983658794757 63850814254985434436024017)
        ·
          refine ⟨47888110691239075827018013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63850814254985434436024017 47888110691239075827018013)
          ·
            refine ⟨17958041509214653435131755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47888110691239075827018013 17958041509214653435131755)
            ·
              refine ⟨26937062263821980152697633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17958041509214653435131755 26937062263821980152697633)
              ·
                refine ⟨20202796697866485114523225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26937062263821980152697633 20202796697866485114523225)
                ·
                  refine ⟨15152097523399863835892419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20202796697866485114523225 15152097523399863835892419)
                  ·
                    refine ⟨22728146285099795753838629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15152097523399863835892419 22728146285099795753838629)
                    ·
                      refine ⟨4261527428456211703844743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22728146285099795753838629 4261527428456211703844743)
                      ·
                        rfl

theorem cell23_8299295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_8299295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299295 prefixEnd_8299295 := by exact prefixLift 8299295
  have htrace : WordTrace (prefixWord ++ tailWord_8299295) baseStart_8299295 baseEnd_8299295 := by
    simpa [prefixWord, tailWord_8299295, baseEnd_8299295] using wordTrace_append hprefix tailTrace_8299295
  have hstable : (prefixWord ++ tailWord_8299295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299295).length < 2 ^ (prefixWord ++ tailWord_8299295).sum := by decide
  have hdescent : baseEnd_8299295 < baseStart_8299295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299328 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_8299328 : Nat := 118140960795 + 8299328 * 2 ^ 59
def prefixEnd_8299328 : Nat := 4983230072969 + 3 ^ 40 * 8299328 * 2
def baseEnd_8299328 : Nat := 4261544373317810074732091

theorem tailTrace_8299328 : CollatzResearch.WordTrace tailWord_8299328 prefixEnd_8299328 4261544373317810074732091 := by
  unfold tailWord_8299328
  simp only [CollatzResearch.WordTrace]
  refine ⟨151350680038479771610773319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201800906717973028814364425 151350680038479771610773319)
  ·
    refine ⟨227026020057719657416159979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151350680038479771610773319 227026020057719657416159979)
    ·
      refine ⟨340539030086579486124239969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227026020057719657416159979 340539030086579486124239969)
      ·
        refine ⟨255404272564934614593179977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340539030086579486124239969 255404272564934614593179977)
        ·
          refine ⟨191553204423700960944884983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255404272564934614593179977 191553204423700960944884983)
          ·
            refine ⟨287329806635551441417327475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191553204423700960944884983 287329806635551441417327475)
            ·
              refine ⟨430994709953327162125991213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287329806635551441417327475 430994709953327162125991213)
              ·
                refine ⟨161623016232497685797246705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430994709953327162125991213 161623016232497685797246705)
                ·
                  refine ⟨121217262174373264347935029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161623016232497685797246705 121217262174373264347935029)
                  ·
                    refine ⟨11364118328847493532618909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121217262174373264347935029 11364118328847493532618909)
                    ·
                      refine ⟨4261544373317810074732091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11364118328847493532618909 4261544373317810074732091)
                      ·
                        rfl

theorem cell23_8299328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_8299328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299328 prefixEnd_8299328 := by exact prefixLift 8299328
  have htrace : WordTrace (prefixWord ++ tailWord_8299328) baseStart_8299328 baseEnd_8299328 := by
    simpa [prefixWord, tailWord_8299328, baseEnd_8299328] using wordTrace_append hprefix tailTrace_8299328
  have hstable : (prefixWord ++ tailWord_8299328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299328).length < 2 ^ (prefixWord ++ tailWord_8299328).sum := by decide
  have hdescent : baseEnd_8299328 < baseStart_8299328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299329 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8299329 : Nat := 118140960795 + 8299329 * 2 ^ 59
def prefixEnd_8299329 : Nat := 4983230072969 + 3 ^ 40 * 8299329 * 2
def baseEnd_8299329 : Nat := 4261544886798464570819587

theorem tailTrace_8299329 : CollatzResearch.WordTrace tailWord_8299329 prefixEnd_8299329 4261544886798464570819587 := by
  unfold tailWord_8299329
  simp only [CollatzResearch.WordTrace]
  refine ⟨302701396549955920392333041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201800931033303946928222027 302701396549955920392333041)
  ·
    refine ⟨227026047412466940294249781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302701396549955920392333041 227026047412466940294249781)
    ·
      refine ⟨21283691944918775652585917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227026047412466940294249781 21283691944918775652585917)
      ·
        refine ⟨7981384479344540869719719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21283691944918775652585917 7981384479344540869719719)
        ·
          refine ⟨11972076719016811304579579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981384479344540869719719 11972076719016811304579579)
          ·
            refine ⟨17958115078525216956869369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972076719016811304579579 17958115078525216956869369)
            ·
              refine ⟨13468586308893912717652027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17958115078525216956869369 13468586308893912717652027)
              ·
                refine ⟨20202879463340869076478041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13468586308893912717652027 20202879463340869076478041)
                ·
                  refine ⟨15152159597505651807358531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20202879463340869076478041 15152159597505651807358531)
                  ·
                    refine ⟨22728239396258477711037797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15152159597505651807358531 22728239396258477711037797)
                    ·
                      refine ⟨4261544886798464570819587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22728239396258477711037797 4261544886798464570819587)
                      ·
                        rfl

theorem cell23_8299329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8299329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299329 prefixEnd_8299329 := by exact prefixLift 8299329
  have htrace : WordTrace (prefixWord ++ tailWord_8299329) baseStart_8299329 baseEnd_8299329 := by
    simpa [prefixWord, tailWord_8299329, baseEnd_8299329] using wordTrace_append hprefix tailTrace_8299329
  have hstable : (prefixWord ++ tailWord_8299329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299329).length < 2 ^ (prefixWord ++ tailWord_8299329).sum := by decide
  have hdescent : baseEnd_8299329 < baseStart_8299329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299355 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 10, 3, 2]
def baseStart_8299355 : Nat := 118140960795 + 8299355 * 2 ^ 59
def prefixEnd_8299355 : Nat := 4983230072969 + 3 ^ 40 * 8299355 * 2
def baseEnd_8299355 : Nat := 4261558237295481469094467

theorem tailTrace_8299355 : CollatzResearch.WordTrace tailWord_8299355 prefixEnd_8299355 4261558237295481469094467 := by
  unfold tailWord_8299355
  simp only [CollatzResearch.WordTrace]
  refine ⟨302702344847861726832779519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201801563231907817888519679 302702344847861726832779519)
  ·
    refine ⟨454053517271792590249169279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302702344847861726832779519 454053517271792590249169279)
    ·
      refine ⟨681080275907688885373753919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454053517271792590249169279 681080275907688885373753919)
      ·
        refine ⟨1021620413861533328060630879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681080275907688885373753919 1021620413861533328060630879)
        ·
          refine ⟨1532430620792299992090946319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021620413861533328060630879 1532430620792299992090946319)
          ·
            refine ⟨2298645931188449988136419479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532430620792299992090946319 2298645931188449988136419479)
            ·
              refine ⟨3447968896782674982204629219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298645931188449988136419479 3447968896782674982204629219)
              ·
                refine ⟨5171953345174012473306943829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447968896782674982204629219 5171953345174012473306943829)
                ·
                  refine ⟨15152207065939489667891437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5171953345174012473306943829 15152207065939489667891437)
                  ·
                    refine ⟨5682077649727308625459289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15152207065939489667891437 5682077649727308625459289)
                    ·
                      refine ⟨4261558237295481469094467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682077649727308625459289 4261558237295481469094467)
                      ·
                        rfl

theorem cell23_8299355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 3, 2].length) (baseStart_8299355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299355 prefixEnd_8299355 := by exact prefixLift 8299355
  have htrace : WordTrace (prefixWord ++ tailWord_8299355) baseStart_8299355 baseEnd_8299355 := by
    simpa [prefixWord, tailWord_8299355, baseEnd_8299355] using wordTrace_append hprefix tailTrace_8299355
  have hstable : (prefixWord ++ tailWord_8299355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299355).length < 2 ^ (prefixWord ++ tailWord_8299355).sum := by decide
  have hdescent : baseEnd_8299355 < baseStart_8299355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299356 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_8299356 : Nat := 118140960795 + 8299356 * 2 ^ 59
def prefixEnd_8299356 : Nat := 4983230072969 + 3 ^ 40 * 8299356 * 2
def baseEnd_8299356 : Nat := 1420519583592045321727321

theorem tailTrace_8299356 : CollatzResearch.WordTrace tailWord_8299356 prefixEnd_8299356 1420519583592045321727321 := by
  unfold tailWord_8299356
  simp only [CollatzResearch.WordTrace]
  refine ⟨151351190660429052001782961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201801587547238736002377281 151351190660429052001782961)
  ·
    refine ⟨113513392995321789001337221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151351190660429052001782961 113513392995321789001337221)
    ·
      refine ⟨21283761186622835437750729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113513392995321789001337221 21283761186622835437750729)
      ·
        refine ⟨15962820889967126578313047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21283761186622835437750729 15962820889967126578313047)
        ·
          refine ⟨23944231334950689867469571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962820889967126578313047 23944231334950689867469571)
          ·
            refine ⟨35916347002426034801204357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23944231334950689867469571 35916347002426034801204357)
            ·
              refine ⟨6734315062954881525225817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35916347002426034801204357 6734315062954881525225817)
              ·
                refine ⟨5050736297216161143919363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734315062954881525225817 5050736297216161143919363)
                ·
                  refine ⟨7576104445824241715879045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050736297216161143919363 7576104445824241715879045)
                  ·
                    refine ⟨1420519583592045321727321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576104445824241715879045 1420519583592045321727321)
                    ·
                      rfl

theorem cell23_8299356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_8299356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299356 prefixEnd_8299356 := by exact prefixLift 8299356
  have htrace : WordTrace (prefixWord ++ tailWord_8299356) baseStart_8299356 baseEnd_8299356 := by
    simpa [prefixWord, tailWord_8299356, baseEnd_8299356] using wordTrace_append hprefix tailTrace_8299356
  have hstable : (prefixWord ++ tailWord_8299356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299356).length < 2 ^ (prefixWord ++ tailWord_8299356).sum := by decide
  have hdescent : baseEnd_8299356 < baseStart_8299356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299382 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_8299382 : Nat := 118140960795 + 8299382 * 2 ^ 59
def prefixEnd_8299382 : Nat := 4983230072969 + 3 ^ 40 * 8299382 * 2
def baseEnd_8299382 : Nat := 1420524033757717621152281

theorem tailTrace_8299382 : CollatzResearch.WordTrace tailWord_8299382 prefixEnd_8299382 1420524033757717621152281 := by
  unfold tailWord_8299382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918958101172744402750775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201802219745842606962674933 18918958101172744402750775)
  ·
    refine ⟨28378437151759116604126163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18918958101172744402750775 28378437151759116604126163)
    ·
      refine ⟨42567655727638674906189245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28378437151759116604126163 42567655727638674906189245)
      ·
        refine ⟨15962870897864503089820967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42567655727638674906189245 15962870897864503089820967)
        ·
          refine ⟨23944306346796754634731451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962870897864503089820967 23944306346796754634731451)
          ·
            refine ⟨35916459520195131952097177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23944306346796754634731451 35916459520195131952097177)
            ·
              refine ⟨26937344640146348964072883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35916459520195131952097177 26937344640146348964072883)
              ·
                refine ⟨40406016960219523446109325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26937344640146348964072883 40406016960219523446109325)
                ·
                  refine ⟨15152256360082321292290997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40406016960219523446109325 15152256360082321292290997)
                  ·
                    refine ⟨1420524033757717621152281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15152256360082321292290997 1420524033757717621152281)
                    ·
                      rfl

theorem cell23_8299382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_8299382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299382 prefixEnd_8299382 := by exact prefixLift 8299382
  have htrace : WordTrace (prefixWord ++ tailWord_8299382) baseStart_8299382 baseEnd_8299382 := by
    simpa [prefixWord, tailWord_8299382, baseEnd_8299382] using wordTrace_append hprefix tailTrace_8299382
  have hstable : (prefixWord ++ tailWord_8299382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299382).length < 2 ^ (prefixWord ++ tailWord_8299382).sum := by decide
  have hdescent : baseEnd_8299382 < baseStart_8299382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299385 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_8299385 : Nat := 118140960795 + 8299385 * 2 ^ 59
def prefixEnd_8299385 : Nat := 4983230072969 + 3 ^ 40 * 8299385 * 2
def baseEnd_8299385 : Nat := 4261573641715116351719329

theorem tailTrace_8299385 : CollatzResearch.WordTrace tailWord_8299385 prefixEnd_8299385 4261573641715116351719329 := by
  unfold tailWord_8299385
  simp only [CollatzResearch.WordTrace]
  refine ⟨302703439037753041956371609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201802292691835361304247739 302703439037753041956371609)
  ·
    refine ⟨227027579278314781467278707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302703439037753041956371609 227027579278314781467278707)
    ·
      refine ⟨340541368917472172200918061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227027579278314781467278707 340541368917472172200918061)
      ·
        refine ⟨127703013344052064575344273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340541368917472172200918061 127703013344052064575344273)
        ·
          refine ⟨95777260008039048431508205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127703013344052064575344273 95777260008039048431508205)
          ·
            refine ⟨35916472503014643161815577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95777260008039048431508205 35916472503014643161815577)
            ·
              refine ⟨26937354377260982371361683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35916472503014643161815577 26937354377260982371361683)
              ·
                refine ⟨40406031565891473557042525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26937354377260982371361683 40406031565891473557042525)
                ·
                  refine ⟨15152261837209302583890947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40406031565891473557042525 15152261837209302583890947)
                  ·
                    refine ⟨22728392755813953875836421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15152261837209302583890947 22728392755813953875836421)
                    ·
                      refine ⟨4261573641715116351719329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22728392755813953875836421 4261573641715116351719329)
                      ·
                        rfl

theorem cell23_8299385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_8299385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299385 prefixEnd_8299385 := by exact prefixLift 8299385
  have htrace : WordTrace (prefixWord ++ tailWord_8299385) baseStart_8299385 baseEnd_8299385 := by
    simpa [prefixWord, tailWord_8299385, baseEnd_8299385] using wordTrace_append hprefix tailTrace_8299385
  have hstable : (prefixWord ++ tailWord_8299385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299385).length < 2 ^ (prefixWord ++ tailWord_8299385).sum := by decide
  have hdescent : baseEnd_8299385 < baseStart_8299385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299395 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 4, 4]
def baseStart_8299395 : Nat := 118140960795 + 8299395 * 2 ^ 59
def prefixEnd_8299395 : Nat := 4983230072969 + 3 ^ 40 * 8299395 * 2
def baseEnd_8299395 : Nat := 1420526258840553770864761

theorem tailTrace_8299395 : CollatzResearch.WordTrace tailWord_8299395 prefixEnd_8299395 1420526258840553770864761 := by
  unfold tailWord_8299395
  simp only [CollatzResearch.WordTrace]
  refine ⟨302703803767716813664235639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201802535845144542442823759 302703803767716813664235639)
  ·
    refine ⟨454055705651575220496353459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302703803767716813664235639 454055705651575220496353459)
    ·
      refine ⟨681083558477362830744530189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454055705651575220496353459 681083558477362830744530189)
      ·
        refine ⟨255406334429011061529198821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681083558477362830744530189 255406334429011061529198821)
        ·
          refine ⟨47888687705439574036724779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255406334429011061529198821 47888687705439574036724779)
          ·
            refine ⟨71833031558159361055087169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47888687705439574036724779 71833031558159361055087169)
            ·
              refine ⟨53874773668619520791315377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71833031558159361055087169 53874773668619520791315377)
              ·
                refine ⟨40406080251464640593486533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53874773668619520791315377 40406080251464640593486533)
                ·
                  refine ⟨7576140047149620111278725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40406080251464640593486533 7576140047149620111278725)
                  ·
                    refine ⟨1420526258840553770864761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576140047149620111278725 1420526258840553770864761)
                    ·
                      rfl

theorem cell23_8299395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 4].length) (baseStart_8299395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299395 prefixEnd_8299395 := by exact prefixLift 8299395
  have htrace : WordTrace (prefixWord ++ tailWord_8299395) baseStart_8299395 baseEnd_8299395 := by
    simpa [prefixWord, tailWord_8299395, baseEnd_8299395] using wordTrace_append hprefix tailTrace_8299395
  have hstable : (prefixWord ++ tailWord_8299395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299395).length < 2 ^ (prefixWord ++ tailWord_8299395).sum := by decide
  have hdescent : baseEnd_8299395 < baseStart_8299395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299399 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 1, 5]
def baseStart_8299399 : Nat := 118140960795 + 8299399 * 2 ^ 59
def prefixEnd_8299399 : Nat := 4983230072969 + 3 ^ 40 * 8299399 * 2
def baseEnd_8299399 : Nat := 1420526943481426432314755

theorem tailTrace_8299399 : CollatzResearch.WordTrace tailWord_8299399 prefixEnd_8299399 1420526943481426432314755 := by
  unfold tailWord_8299399
  simp only [CollatzResearch.WordTrace]
  refine ⟨302703949659702322347381251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201802633106468214898254167 302703949659702322347381251)
  ·
    refine ⟨454055924489553483521071877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302703949659702322347381251 454055924489553483521071877)
    ·
      refine ⟨85135485841791278160200977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454055924489553483521071877 85135485841791278160200977)
      ·
        refine ⟨63851614381343458620150733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85135485841791278160200977 63851614381343458620150733)
        ·
          refine ⟨23944355393003796982556525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63851614381343458620150733 23944355393003796982556525)
          ·
            refine ⟨8979133272376423868458697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23944355393003796982556525 8979133272376423868458697)
            ·
              refine ⟨6734349954282317901344023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979133272376423868458697 6734349954282317901344023)
              ·
                refine ⟨10101524931423476852016035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734349954282317901344023 10101524931423476852016035)
                ·
                  refine ⟨15152287397135215278024053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10101524931423476852016035 15152287397135215278024053)
                  ·
                    refine ⟨1420526943481426432314755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15152287397135215278024053 1420526943481426432314755)
                    ·
                      rfl

theorem cell23_8299399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_8299399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299399 prefixEnd_8299399 := by exact prefixLift 8299399
  have htrace : WordTrace (prefixWord ++ tailWord_8299399) baseStart_8299399 baseEnd_8299399 := by
    simpa [prefixWord, tailWord_8299399, baseEnd_8299399] using wordTrace_append hprefix tailTrace_8299399
  have hstable : (prefixWord ++ tailWord_8299399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299399).length < 2 ^ (prefixWord ++ tailWord_8299399).sum := by decide
  have hdescent : baseEnd_8299399 < baseStart_8299399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299412 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_8299412 : Nat := 118140960795 + 8299412 * 2 ^ 59
def prefixEnd_8299412 : Nat := 4983230072969 + 3 ^ 40 * 8299412 * 2
def baseEnd_8299412 : Nat := 1420529168564262582027235

theorem tailTrace_8299412 : CollatzResearch.WordTrace tailWord_8299412 prefixEnd_8299412 1420529168564262582027235 := by
  unfold tailWord_8299412
  simp only [CollatzResearch.WordTrace]
  refine ⟨151352211904327612783802245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201802949205770150378402993 151352211904327612783802245)
  ·
    refine ⟨28378539732061427396962921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151352211904327612783802245 28378539732061427396962921)
    ·
      refine ⟨21283904799046070547722191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28378539732061427396962921 21283904799046070547722191)
      ·
        refine ⟨31925857198569105821583287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21283904799046070547722191 31925857198569105821583287)
        ·
          refine ⟨47888785797853658732374931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31925857198569105821583287 47888785797853658732374931)
          ·
            refine ⟨71833178696780488098562397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47888785797853658732374931 71833178696780488098562397)
            ·
              refine ⟨26937442011292683036960899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71833178696780488098562397 26937442011292683036960899)
              ·
                refine ⟨40406163016939024555441349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26937442011292683036960899 40406163016939024555441349)
                ·
                  refine ⟨7576155565676067104145253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40406163016939024555441349 7576155565676067104145253)
                  ·
                    refine ⟨1420529168564262582027235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576155565676067104145253 1420529168564262582027235)
                    ·
                      rfl

theorem cell23_8299412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_8299412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299412 prefixEnd_8299412 := by exact prefixLift 8299412
  have htrace : WordTrace (prefixWord ++ tailWord_8299412) baseStart_8299412 baseEnd_8299412 := by
    simpa [prefixWord, tailWord_8299412, baseEnd_8299412] using wordTrace_append hprefix tailTrace_8299412
  have hstable : (prefixWord ++ tailWord_8299412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299412).length < 2 ^ (prefixWord ++ tailWord_8299412).sum := by decide
  have hdescent : baseEnd_8299412 < baseStart_8299412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299545 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_8299545 : Nat := 118140960795 + 8299545 * 2 ^ 59
def prefixEnd_8299545 : Nat := 4983230072969 + 3 ^ 40 * 8299545 * 2
def baseEnd_8299545 : Nat := 1420551932873278575239531

theorem tailTrace_8299545 : CollatzResearch.WordTrace tailWord_8299545 prefixEnd_8299545 1420551932873278575239531 := by
  unfold tailWord_8299545
  simp only [CollatzResearch.WordTrace]
  refine ⟨302709274717173389282196089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201806183144782259521464059 302709274717173389282196089)
  ·
    refine ⟨227031956037880041961647067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302709274717173389282196089 227031956037880041961647067)
    ·
      refine ⟨340547934056820062942470601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227031956037880041961647067 340547934056820062942470601)
      ·
        refine ⟨255410950542615047206852951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340547934056820062942470601 255410950542615047206852951)
        ·
          refine ⟨383116425813922570810279427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255410950542615047206852951 383116425813922570810279427)
          ·
            refine ⟨574674638720883856215419141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383116425813922570810279427 574674638720883856215419141)
            ·
              refine ⟨107751494760165723040391089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574674638720883856215419141 107751494760165723040391089)
              ·
                refine ⟨80813621070124292280293317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107751494760165723040391089 80813621070124292280293317)
                ·
                  refine ⟨15152553950648304802554997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80813621070124292280293317 15152553950648304802554997)
                  ·
                    refine ⟨1420551932873278575239531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15152553950648304802554997 1420551932873278575239531)
                    ·
                      rfl

theorem cell23_8299545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_8299545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299545 prefixEnd_8299545 := by exact prefixLift 8299545
  have htrace : WordTrace (prefixWord ++ tailWord_8299545) baseStart_8299545 baseEnd_8299545 := by
    simpa [prefixWord, tailWord_8299545, baseEnd_8299545] using wordTrace_append hprefix tailTrace_8299545
  have hstable : (prefixWord ++ tailWord_8299545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299545).length < 2 ^ (prefixWord ++ tailWord_8299545).sum := by decide
  have hdescent : baseEnd_8299545 < baseStart_8299545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299595 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_8299595 : Nat := 118140960795 + 8299595 * 2 ^ 59
def prefixEnd_8299595 : Nat := 4983230072969 + 3 ^ 40 * 8299595 * 2
def baseEnd_8299595 : Nat := 4261681472652560530093363

theorem tailTrace_8299595 : CollatzResearch.WordTrace tailWord_8299595 prefixEnd_8299595 4261681472652560530093363 := by
  unfold tailWord_8299595
  simp only [CollatzResearch.WordTrace]
  refine ⟨302711098366992247821516239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201807398911328165214344159 302711098366992247821516239)
  ·
    refine ⟨454066647550488371732274359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302711098366992247821516239 454066647550488371732274359)
    ·
      refine ⟨681099971325732557598411539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454066647550488371732274359 681099971325732557598411539)
      ·
        refine ⟨1021649956988598836397617309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681099971325732557598411539 1021649956988598836397617309)
        ·
          refine ⟨383118733870724563649106491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1021649956988598836397617309 383118733870724563649106491)
          ·
            refine ⟨574678100806086845473659737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383118733870724563649106491 574678100806086845473659737)
            ·
              refine ⟨431008575604565134105244803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574678100806086845473659737 431008575604565134105244803)
              ·
                refine ⟨646512863406847701157867205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431008575604565134105244803 646512863406847701157867205)
                ·
                  refine ⟨121221161888783943967100101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646512863406847701157867205 121221161888783943967100101)
                  ·
                    refine ⟨22728967854146989493831269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121221161888783943967100101 22728967854146989493831269)
                    ·
                      refine ⟨4261681472652560530093363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22728967854146989493831269 4261681472652560530093363)
                      ·
                        rfl

theorem cell23_8299595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_8299595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299595 prefixEnd_8299595 := by exact prefixLift 8299595
  have htrace : WordTrace (prefixWord ++ tailWord_8299595) baseStart_8299595 baseEnd_8299595 := by
    simpa [prefixWord, tailWord_8299595, baseEnd_8299595] using wordTrace_append hprefix tailTrace_8299595
  have hstable : (prefixWord ++ tailWord_8299595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299595).length < 2 ^ (prefixWord ++ tailWord_8299595).sum := by decide
  have hdescent : baseEnd_8299595 < baseStart_8299595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299612 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_8299612 : Nat := 118140960795 + 8299612 * 2 ^ 59
def prefixEnd_8299612 : Nat := 4983230072969 + 3 ^ 40 * 8299612 * 2
def baseEnd_8299612 : Nat := 4261690201823686963580785

theorem tailTrace_8299612 : CollatzResearch.WordTrace tailWord_8299612 prefixEnd_8299612 4261690201823686963580785 := by
  unfold tailWord_8299612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151355859203965329862442545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201807812271953773149923393 151355859203965329862442545)
  ·
    refine ⟨113516894402973997396831909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151355859203965329862442545 113516894402973997396831909)
    ·
      refine ⟨21284417700557624511905983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113516894402973997396831909 21284417700557624511905983)
      ·
        refine ⟨31926626550836436767858975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21284417700557624511905983 31926626550836436767858975)
        ·
          refine ⟨47889939826254655151788463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31926626550836436767858975 47889939826254655151788463)
          ·
            refine ⟨71834909739381982727682695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47889939826254655151788463 71834909739381982727682695)
            ·
              refine ⟨107752364609072974091524043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71834909739381982727682695 107752364609072974091524043)
              ·
                refine ⟨161628546913609461137286065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107752364609072974091524043 161628546913609461137286065)
                ·
                  refine ⟨121221410185207095852964549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161628546913609461137286065 121221410185207095852964549)
                  ·
                    refine ⟨22729014409726330472430853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121221410185207095852964549 22729014409726330472430853)
                    ·
                      refine ⟨4261690201823686963580785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22729014409726330472430853 4261690201823686963580785)
                      ·
                        rfl

theorem cell23_8299612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_8299612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299612 prefixEnd_8299612 := by exact prefixLift 8299612
  have htrace : WordTrace (prefixWord ++ tailWord_8299612) baseStart_8299612 baseEnd_8299612 := by
    simpa [prefixWord, tailWord_8299612, baseEnd_8299612] using wordTrace_append hprefix tailTrace_8299612
  have hstable : (prefixWord ++ tailWord_8299612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299612).length < 2 ^ (prefixWord ++ tailWord_8299612).sum := by decide
  have hdescent : baseEnd_8299612 < baseStart_8299612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299676 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_8299676 : Nat := 118140960795 + 8299676 * 2 ^ 59
def prefixEnd_8299676 : Nat := 4983230072969 + 3 ^ 40 * 8299676 * 2
def baseEnd_8299676 : Nat := 4261723064585574713180491

theorem tailTrace_8299676 : CollatzResearch.WordTrace tailWord_8299676 prefixEnd_8299676 4261723064585574713180491 := by
  unfold tailWord_8299676
  simp only [CollatzResearch.WordTrace]
  refine ⟨151357026339849399327607441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201809368453132532436809921 151357026339849399327607441)
  ·
    refine ⟨113517769754887049495705581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151357026339849399327607441 113517769754887049495705581)
    ·
      refine ⟨42569163658082643560889593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113517769754887049495705581 42569163658082643560889593)
      ·
        refine ⟨31926872743561982670667195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42569163658082643560889593 31926872743561982670667195)
        ·
          refine ⟨47890309115342974006000793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31926872743561982670667195 47890309115342974006000793)
          ·
            refine ⟨35917731836507230504500595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47890309115342974006000793 35917731836507230504500595)
            ·
              refine ⟨53876597754760845756750893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35917731836507230504500595 53876597754760845756750893)
              ·
                refine ⟨20203724158035317158781585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53876597754760845756750893 20203724158035317158781585)
                ·
                  refine ⟨15152793118526487869086189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20203724158035317158781585 15152793118526487869086189)
                  ·
                    refine ⟨5682297419447432950907321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15152793118526487869086189 5682297419447432950907321)
                    ·
                      refine ⟨4261723064585574713180491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682297419447432950907321 4261723064585574713180491)
                      ·
                        rfl

theorem cell23_8299676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_8299676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299676 prefixEnd_8299676 := by exact prefixLift 8299676
  have htrace : WordTrace (prefixWord ++ tailWord_8299676) baseStart_8299676 baseEnd_8299676 := by
    simpa [prefixWord, tailWord_8299676, baseEnd_8299676] using wordTrace_append hprefix tailTrace_8299676
  have hstable : (prefixWord ++ tailWord_8299676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299676).length < 2 ^ (prefixWord ++ tailWord_8299676).sum := by decide
  have hdescent : baseEnd_8299676 < baseStart_8299676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299692 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_8299692 : Nat := 118140960795 + 8299692 * 2 ^ 59
def prefixEnd_8299692 : Nat := 4983230072969 + 3 ^ 40 * 8299692 * 2
def baseEnd_8299692 : Nat := 4261731280276046650580417

theorem tailTrace_8299692 : CollatzResearch.WordTrace tailWord_8299692 prefixEnd_8299692 4261731280276046650580417 := by
  unfold tailWord_8299692
  simp only [CollatzResearch.WordTrace]
  refine ⟨151357318123820416693898665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201809757498427222258531553 151357318123820416693898665)
  ·
    refine ⟨113517988592865312520423999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151357318123820416693898665 113517988592865312520423999)
    ·
      refine ⟨170276982889297968780635999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113517988592865312520423999 170276982889297968780635999)
      ·
        refine ⟨255415474333946953170953999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170276982889297968780635999 255415474333946953170953999)
        ·
          refine ⟨383123211500920429756430999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255415474333946953170953999 383123211500920429756430999)
          ·
            refine ⟨574684817251380644634646499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383123211500920429756430999 574684817251380644634646499)
            ·
              refine ⟨862027225877070966951969749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574684817251380644634646499 862027225877070966951969749)
              ·
                refine ⟨20203763106493850787936791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 862027225877070966951969749 20203763106493850787936791)
                ·
                  refine ⟨30305644659740776181905187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20203763106493850787936791 30305644659740776181905187)
                  ·
                    refine ⟨45458466989611164272857781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30305644659740776181905187 45458466989611164272857781)
                    ·
                      refine ⟨4261731280276046650580417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45458466989611164272857781 4261731280276046650580417)
                      ·
                        rfl

theorem cell23_8299692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_8299692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299692 prefixEnd_8299692 := by exact prefixLift 8299692
  have htrace : WordTrace (prefixWord ++ tailWord_8299692) baseStart_8299692 baseEnd_8299692 := by
    simpa [prefixWord, tailWord_8299692, baseEnd_8299692] using wordTrace_append hprefix tailTrace_8299692
  have hstable : (prefixWord ++ tailWord_8299692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299692).length < 2 ^ (prefixWord ++ tailWord_8299692).sum := by decide
  have hdescent : baseEnd_8299692 < baseStart_8299692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299699 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 2, 4]
def baseStart_8299699 : Nat := 118140960795 + 8299699 * 2 ^ 59
def prefixEnd_8299699 : Nat := 4983230072969 + 3 ^ 40 * 8299699 * 2
def baseEnd_8299699 : Nat := 1420578291546876041064295

theorem tailTrace_8299699 : CollatzResearch.WordTrace tailWord_8299699 prefixEnd_8299699 1420578291546876041064295 := by
  unfold tailWord_8299699
  simp only [CollatzResearch.WordTrace]
  refine ⟨302714891558615473583302151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201809927705743649055534767 302714891558615473583302151)
  ·
    refine ⟨454072337337923210374953227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302714891558615473583302151 454072337337923210374953227)
    ·
      refine ⟨681108506006884815562429841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454072337337923210374953227 681108506006884815562429841)
      ·
        refine ⟨510831379505163611671822381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681108506006884815562429841 510831379505163611671822381)
        ·
          refine ⟨191561767314436354376933393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510831379505163611671822381 191561767314436354376933393)
          ·
            refine ⟨143671325485827265782700045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191561767314436354376933393 143671325485827265782700045)
            ·
              refine ⟨53876747057185224668512517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143671325485827265782700045 53876747057185224668512517)
              ·
                refine ⟨10101890073222229625346097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53876747057185224668512517 10101890073222229625346097)
                ·
                  refine ⟨7576417554916672219009573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10101890073222229625346097 7576417554916672219009573)
                  ·
                    refine ⟨1420578291546876041064295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576417554916672219009573 1420578291546876041064295)
                    ·
                      rfl

theorem cell23_8299699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 4].length) (baseStart_8299699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299699 prefixEnd_8299699 := by exact prefixLift 8299699
  have htrace : WordTrace (prefixWord ++ tailWord_8299699) baseStart_8299699 baseEnd_8299699 := by
    simpa [prefixWord, tailWord_8299699, baseEnd_8299699] using wordTrace_append hprefix tailTrace_8299699
  have hstable : (prefixWord ++ tailWord_8299699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299699).length < 2 ^ (prefixWord ++ tailWord_8299699).sum := by decide
  have hdescent : baseEnd_8299699 < baseStart_8299699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299706 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_8299706 : Nat := 118140960795 + 8299706 * 2 ^ 59
def prefixEnd_8299706 : Nat := 4983230072969 + 3 ^ 40 * 8299706 * 2
def baseEnd_8299706 : Nat := 4261738469005209595805353

theorem tailTrace_8299706 : CollatzResearch.WordTrace tailWord_8299706 prefixEnd_8299706 4261738469005209595805353 := by
  unfold tailWord_8299706
  simp only [CollatzResearch.WordTrace]
  refine ⟨75678786717397528444701743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201810097913060075852537981 75678786717397528444701743)
  ·
    refine ⟨113518180076096292667052615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75678786717397528444701743 113518180076096292667052615)
    ·
      refine ⟨170277270114144439000578923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113518180076096292667052615 170277270114144439000578923)
      ·
        refine ⟨255415905171216658500868385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170277270114144439000578923 255415905171216658500868385)
        ·
          refine ⟨191561928878412493875651289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255415905171216658500868385 191561928878412493875651289)
          ·
            refine ⟨143671446658809370406738467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191561928878412493875651289 143671446658809370406738467)
            ·
              refine ⟨215507169988214055610107701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143671446658809370406738467 215507169988214055610107701)
              ·
                refine ⟨20203797186395067713447597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215507169988214055610107701 20203797186395067713447597)
                ·
                  refine ⟨7576423944898150392542849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20203797186395067713447597 7576423944898150392542849)
                  ·
                    refine ⟨5682317958673612794407137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7576423944898150392542849 5682317958673612794407137)
                    ·
                      refine ⟨4261738469005209595805353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682317958673612794407137 4261738469005209595805353)
                      ·
                        rfl

theorem cell23_8299706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_8299706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299706 prefixEnd_8299706 := by exact prefixLift 8299706
  have htrace : WordTrace (prefixWord ++ tailWord_8299706) baseStart_8299706 baseEnd_8299706 := by
    simpa [prefixWord, tailWord_8299706, baseEnd_8299706] using wordTrace_append hprefix tailTrace_8299706
  have hstable : (prefixWord ++ tailWord_8299706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299706).length < 2 ^ (prefixWord ++ tailWord_8299706).sum := by decide
  have hdescent : baseEnd_8299706 < baseStart_8299706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299709 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_8299709 : Nat := 118140960795 + 8299709 * 2 ^ 59
def prefixEnd_8299709 : Nat := 4983230072969 + 3 ^ 40 * 8299709 * 2
def baseEnd_8299709 : Nat := 4261740009447173084067839

theorem tailTrace_8299709 : CollatzResearch.WordTrace tailWord_8299709 prefixEnd_8299709 4261740009447173084067839 := by
  unfold tailWord_8299709
  simp only [CollatzResearch.WordTrace]
  refine ⟨302715256288579245291166181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201810170859052830194110787 302715256288579245291166181)
  ·
    refine ⟨56759110554108608492093659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302715256288579245291166181 56759110554108608492093659)
    ·
      refine ⟨85138665831162912738140489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56759110554108608492093659 85138665831162912738140489)
      ·
        refine ⟨63853999373372184553605367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85138665831162912738140489 63853999373372184553605367)
        ·
          refine ⟨95780999060058276830408051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63853999373372184553605367 95780999060058276830408051)
          ·
            refine ⟨143671498590087415245612077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95780999060058276830408051 143671498590087415245612077)
            ·
              refine ⟨53876811971282780717104529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143671498590087415245612077 53876811971282780717104529)
              ·
                refine ⟨40407608978462085537828397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53876811971282780717104529 40407608978462085537828397)
                ·
                  refine ⟨15152853366923282076685649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40407608978462085537828397 15152853366923282076685649)
                  ·
                    refine ⟨11364640025192461557514237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15152853366923282076685649 11364640025192461557514237)
                    ·
                      refine ⟨4261740009447173084067839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11364640025192461557514237 4261740009447173084067839)
                      ·
                        rfl

theorem cell23_8299709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_8299709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299709 prefixEnd_8299709 := by exact prefixLift 8299709
  have htrace : WordTrace (prefixWord ++ tailWord_8299709) baseStart_8299709 baseEnd_8299709 := by
    simpa [prefixWord, tailWord_8299709, baseEnd_8299709] using wordTrace_append hprefix tailTrace_8299709
  have hstable : (prefixWord ++ tailWord_8299709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299709).length < 2 ^ (prefixWord ++ tailWord_8299709).sum := by decide
  have hdescent : baseEnd_8299709 < baseStart_8299709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299716 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_8299716 : Nat := 118140960795 + 8299716 * 2 ^ 59
def prefixEnd_8299716 : Nat := 4983230072969 + 3 ^ 40 * 8299716 * 2
def baseEnd_8299716 : Nat := 1420581201270584852226769

theorem tailTrace_8299716 : CollatzResearch.WordTrace tailWord_8299716 prefixEnd_8299716 1420581201270584852226769 := by
  unfold tailWord_8299716
  simp only [CollatzResearch.WordTrace]
  refine ⟨151357755799776942743335501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201810341066369256991114001 151357755799776942743335501)
  ·
    refine ⟨56759158424916353528750813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151357755799776942743335501 56759158424916353528750813)
    ·
      refine ⟨21284684409343632573281555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56759158424916353528750813 21284684409343632573281555)
      ·
        refine ⟨31927026614015448859922333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21284684409343632573281555 31927026614015448859922333)
        ·
          refine ⟨11972634980255793322470875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31927026614015448859922333 11972634980255793322470875)
          ·
            refine ⟨17958952470383689983706313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972634980255793322470875 17958952470383689983706313)
            ·
              refine ⟨13469214352787767487779735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17958952470383689983706313 13469214352787767487779735)
              ·
                refine ⟨20203821529181651231669603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13469214352787767487779735 20203821529181651231669603)
                ·
                  refine ⟨30305732293772476847504405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20203821529181651231669603 30305732293772476847504405)
                  ·
                    refine ⟨1420581201270584852226769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30305732293772476847504405 1420581201270584852226769)
                    ·
                      rfl

theorem cell23_8299716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_8299716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299716 prefixEnd_8299716 := by exact prefixLift 8299716
  have htrace : WordTrace (prefixWord ++ tailWord_8299716) baseStart_8299716 baseEnd_8299716 := by
    simpa [prefixWord, tailWord_8299716, baseEnd_8299716] using wordTrace_append hprefix tailTrace_8299716
  have hstable : (prefixWord ++ tailWord_8299716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299716).length < 2 ^ (prefixWord ++ tailWord_8299716).sum := by decide
  have hdescent : baseEnd_8299716 < baseStart_8299716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299756 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_8299756 : Nat := 118140960795 + 8299756 * 2 ^ 59
def prefixEnd_8299756 : Nat := 4983230072969 + 3 ^ 40 * 8299756 * 2
def baseEnd_8299756 : Nat := 4261764143037934400180123

theorem tailTrace_8299756 : CollatzResearch.WordTrace tailWord_8299756 prefixEnd_8299756 4261764143037934400180123 := by
  unfold tailWord_8299756
  simp only [CollatzResearch.WordTrace]
  refine ⟨151358485259704486159063561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201811313679605981545418081 151358485259704486159063561)
  ·
    refine ⟨113518863944778364619297671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151358485259704486159063561 113518863944778364619297671)
    ·
      refine ⟨170278295917167546928946507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113518863944778364619297671 170278295917167546928946507)
      ·
        refine ⟨255417443875751320393419761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170278295917167546928946507 255417443875751320393419761)
        ·
          refine ⟨191563082906813490295064821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255417443875751320393419761 191563082906813490295064821)
          ·
            refine ⟨17959039022513764715162327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191563082906813490295064821 17959039022513764715162327)
            ·
              refine ⟨26938558533770647072743491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959039022513764715162327 26938558533770647072743491)
              ·
                refine ⟨40407837800655970609115237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26938558533770647072743491 40407837800655970609115237)
                ·
                  refine ⟨7576469587622994489209107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40407837800655970609115237 7576469587622994489209107)
                  ·
                    refine ⟨11364704381434491733813661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576469587622994489209107 11364704381434491733813661)
                    ·
                      refine ⟨4261764143037934400180123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11364704381434491733813661 4261764143037934400180123)
                      ·
                        rfl

theorem cell23_8299756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_8299756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299756 prefixEnd_8299756 := by exact prefixLift 8299756
  have htrace : WordTrace (prefixWord ++ tailWord_8299756) baseStart_8299756 baseEnd_8299756 := by
    simpa [prefixWord, tailWord_8299756, baseEnd_8299756] using wordTrace_append hprefix tailTrace_8299756
  have hstable : (prefixWord ++ tailWord_8299756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299756).length < 2 ^ (prefixWord ++ tailWord_8299756).sum := by decide
  have hdescent : baseEnd_8299756 < baseStart_8299756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299799 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_8299799 : Nat := 118140960795 + 8299799 * 2 ^ 59
def prefixEnd_8299799 : Nat := 4983230072969 + 3 ^ 40 * 8299799 * 2
def baseEnd_8299799 : Nat := 4261786222706077731942425

theorem tailTrace_8299799 : CollatzResearch.WordTrace tailWord_8299799 prefixEnd_8299799 4261786222706077731942425 := by
  unfold tailWord_8299799
  simp only [CollatzResearch.WordTrace]
  refine ⟨302718538858253190661942451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201812359238835460441294967 302718538858253190661942451)
  ·
    refine ⟨454077808287379785992913677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302718538858253190661942451 454077808287379785992913677)
    ·
      refine ⟨170279178107767419747342629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454077808287379785992913677 170279178107767419747342629)
      ·
        refine ⟨31927345895206391202626743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170279178107767419747342629 31927345895206391202626743)
        ·
          refine ⟨47891018842809586803940115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31927345895206391202626743 47891018842809586803940115)
          ·
            refine ⟨71836528264214380205910173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47891018842809586803940115 71836528264214380205910173)
            ·
              refine ⟨26938698099080392577216315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71836528264214380205910173 26938698099080392577216315)
              ·
                refine ⟨40408047148620588865824473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26938698099080392577216315 40408047148620588865824473)
                ·
                  refine ⟨30306035361465441649368355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40408047148620588865824473 30306035361465441649368355)
                  ·
                    refine ⟨45459053042198162474052533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30306035361465441649368355 45459053042198162474052533)
                    ·
                      refine ⟨4261786222706077731942425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45459053042198162474052533 4261786222706077731942425)
                      ·
                        rfl

theorem cell23_8299799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_8299799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299799 prefixEnd_8299799 := by exact prefixLift 8299799
  have htrace : WordTrace (prefixWord ++ tailWord_8299799) baseStart_8299799 baseEnd_8299799 := by
    simpa [prefixWord, tailWord_8299799, baseEnd_8299799] using wordTrace_append hprefix tailTrace_8299799
  have hstable : (prefixWord ++ tailWord_8299799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299799).length < 2 ^ (prefixWord ++ tailWord_8299799).sum := by decide
  have hdescent : baseEnd_8299799 < baseStart_8299799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299813 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_8299813 : Nat := 118140960795 + 8299813 * 2 ^ 59
def prefixEnd_8299813 : Nat := 4983230072969 + 3 ^ 40 * 8299813 * 2
def baseEnd_8299813 : Nat := 4261793411435240677167361

theorem tailTrace_8299813 : CollatzResearch.WordTrace tailWord_8299813 prefixEnd_8299813 4261793411435240677167361 := by
  unfold tailWord_8299813
  simp only [CollatzResearch.WordTrace]
  refine ⟨302719049480202471052952093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201812699653468314035301395 302719049480202471052952093)
  ·
    refine ⟨113519643555075926644857035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302719049480202471052952093 113519643555075926644857035)
    ·
      refine ⟨170279465332613889967285553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113519643555075926644857035 170279465332613889967285553)
      ·
        refine ⟨127709598999460417475464165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170279465332613889967285553 127709598999460417475464165)
        ·
          refine ⟨23945549812398828276649531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127709598999460417475464165 23945549812398828276649531)
          ·
            refine ⟨35918324718598242414974297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23945549812398828276649531 35918324718598242414974297)
            ·
              refine ⟨26938743538948681811230723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35918324718598242414974297 26938743538948681811230723)
              ·
                refine ⟨40408115308423022716846085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26938743538948681811230723 40408115308423022716846085)
                ·
                  refine ⟨7576521620329316759408641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40408115308423022716846085 7576521620329316759408641)
                  ·
                    refine ⟨5682391215246987569556481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7576521620329316759408641 5682391215246987569556481)
                    ·
                      refine ⟨4261793411435240677167361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682391215246987569556481 4261793411435240677167361)
                      ·
                        rfl

theorem cell23_8299813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_8299813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299813 prefixEnd_8299813 := by exact prefixLift 8299813
  have htrace : WordTrace (prefixWord ++ tailWord_8299813) baseStart_8299813 baseEnd_8299813 := by
    simpa [prefixWord, tailWord_8299813, baseEnd_8299813] using wordTrace_append hprefix tailTrace_8299813
  have hstable : (prefixWord ++ tailWord_8299813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299813).length < 2 ^ (prefixWord ++ tailWord_8299813).sum := by decide
  have hdescent : baseEnd_8299813 < baseStart_8299813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299849 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_8299849 : Nat := 118140960795 + 8299849 * 2 ^ 59
def prefixEnd_8299849 : Nat := 4983230072969 + 3 ^ 40 * 8299849 * 2
def baseEnd_8299849 : Nat := 1420603965579600845439065

theorem tailTrace_8299849 : CollatzResearch.WordTrace tailWord_8299849 prefixEnd_8299849 1420603965579600845439065 := by
  unfold tailWord_8299849
  simp only [CollatzResearch.WordTrace]
  refine ⟨302720362508072049201262601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201813575005381366134175067 302720362508072049201262601)
  ·
    refine ⟨227040271881054036900946951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302720362508072049201262601 227040271881054036900946951)
    ·
      refine ⟨340560407821581055351420427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227040271881054036900946951 340560407821581055351420427)
      ·
        refine ⟨510840611732371583027130641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340560407821581055351420427 510840611732371583027130641)
        ·
          refine ⟨383130458799278687270347981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510840611732371583027130641 383130458799278687270347981)
          ·
            refine ⟨143673922049729507726380493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383130458799278687270347981 143673922049729507726380493)
            ·
              refine ⟨53877720768648565397392685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143673922049729507726380493 53877720768648565397392685)
              ·
                refine ⟨20204145288243212024022257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53877720768648565397392685 20204145288243212024022257)
                ·
                  refine ⟨15153108966182409018016693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20204145288243212024022257 15153108966182409018016693)
                  ·
                    refine ⟨1420603965579600845439065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15153108966182409018016693 1420603965579600845439065)
                    ·
                      rfl

theorem cell23_8299849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_8299849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299849 prefixEnd_8299849 := by exact prefixLift 8299849
  have htrace : WordTrace (prefixWord ++ tailWord_8299849) baseStart_8299849 baseEnd_8299849 := by
    simpa [prefixWord, tailWord_8299849, baseEnd_8299849] using wordTrace_append hprefix tailTrace_8299849
  have hstable : (prefixWord ++ tailWord_8299849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299849).length < 2 ^ (prefixWord ++ tailWord_8299849).sum := by decide
  have hdescent : baseEnd_8299849 < baseStart_8299849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299929 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_8299929 : Nat := 118140960795 + 8299929 * 2 ^ 59
def prefixEnd_8299929 : Nat := 4983230072969 + 3 ^ 40 * 8299929 * 2
def baseEnd_8299929 : Nat := 4261852975191162223316827

theorem tailTrace_8299929 : CollatzResearch.WordTrace tailWord_8299929 prefixEnd_8299929 4261852975191162223316827 := by
  unfold tailWord_8299929
  simp only [CollatzResearch.WordTrace]
  refine ⟨302723280347782222864174841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201815520231854815242783227 302723280347782222864174841)
  ·
    refine ⟨227042460260836667148131131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302723280347782222864174841 227042460260836667148131131)
    ·
      refine ⟨340563690391255000722196697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227042460260836667148131131 340563690391255000722196697)
      ·
        refine ⟨255422767793441250541647523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340563690391255000722196697 255422767793441250541647523)
        ·
          refine ⟨383134151690161875812471285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255422767793441250541647523 383134151690161875812471285)
          ·
            refine ⟨35918826720952675857419183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383134151690161875812471285 35918826720952675857419183)
            ·
              refine ⟨53878240081429013786128775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35918826720952675857419183 53878240081429013786128775)
              ·
                refine ⟨80817360122143520679193163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53878240081429013786128775 80817360122143520679193163)
                ·
                  refine ⟨121226040183215281018789745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80817360122143520679193163 121226040183215281018789745)
                  ·
                    refine ⟨90919530137411460764092309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121226040183215281018789745 90919530137411460764092309)
                    ·
                      refine ⟨4261852975191162223316827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90919530137411460764092309 4261852975191162223316827)
                      ·
                        rfl

theorem cell23_8299929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_8299929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299929 prefixEnd_8299929 := by exact prefixLift 8299929
  have htrace : WordTrace (prefixWord ++ tailWord_8299929) baseStart_8299929 baseEnd_8299929 := by
    simpa [prefixWord, tailWord_8299929, baseEnd_8299929] using wordTrace_append hprefix tailTrace_8299929
  have hstable : (prefixWord ++ tailWord_8299929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299929).length < 2 ^ (prefixWord ++ tailWord_8299929).sum := by decide
  have hdescent : baseEnd_8299929 < baseStart_8299929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299943 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 6]
def baseStart_8299943 : Nat := 118140960795 + 8299943 * 2 ^ 59
def prefixEnd_8299943 : Nat := 4983230072969 + 3 ^ 40 * 8299943 * 2
def baseEnd_8299943 : Nat := 473540018213369463171307

theorem tailTrace_8299943 : CollatzResearch.WordTrace tailWord_8299943 prefixEnd_8299943 473540018213369463171307 := by
  unfold tailWord_8299943
  simp only [CollatzResearch.WordTrace]
  refine ⟨302723790969731503255184483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201815860646487668836789655 302723790969731503255184483)
  ·
    refine ⟨454085686454597254882776725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302723790969731503255184483 454085686454597254882776725)
    ·
      refine ⟨21285266552559246322630159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 454085686454597254882776725 21285266552559246322630159)
      ·
        refine ⟨31927899828838869483945239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21285266552559246322630159 31927899828838869483945239)
        ·
          refine ⟨47891849743258304225917859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31927899828838869483945239 47891849743258304225917859)
          ·
            refine ⟨71837774614887456338876789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47891849743258304225917859 71837774614887456338876789)
            ·
              refine ⟨6734791370145699031769699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71837774614887456338876789 6734791370145699031769699)
              ·
                refine ⟨10102187055218548547654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734791370145699031769699 10102187055218548547654549)
                ·
                  refine ⟨473540018213369463171307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10102187055218548547654549 473540018213369463171307)
                  ·
                    rfl

theorem cell23_8299943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 6].length) (baseStart_8299943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299943 prefixEnd_8299943 := by exact prefixLift 8299943
  have htrace : WordTrace (prefixWord ++ tailWord_8299943) baseStart_8299943 baseEnd_8299943 := by
    simpa [prefixWord, tailWord_8299943, baseEnd_8299943] using wordTrace_append hprefix tailTrace_8299943
  have hstable : (prefixWord ++ tailWord_8299943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299943).length < 2 ^ (prefixWord ++ tailWord_8299943).sum := by decide
  have hdescent : baseEnd_8299943 < baseStart_8299943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299953 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_8299953 : Nat := 118140960795 + 8299953 * 2 ^ 59
def prefixEnd_8299953 : Nat := 4983230072969 + 3 ^ 40 * 8299953 * 2
def baseEnd_8299953 : Nat := 4261865298726870129416717

theorem tailTrace_8299953 : CollatzResearch.WordTrace tailWord_8299953 prefixEnd_8299953 4261865298726870129416717 := by
  unfold tailWord_8299953
  simp only [CollatzResearch.WordTrace]
  refine ⟨302724155699695274963048513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201816103799796849975365675 302724155699695274963048513)
  ·
    refine ⟨227043116774771456222286385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302724155699695274963048513 227043116774771456222286385)
    ·
      refine ⟨170282337581078592166714789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227043116774771456222286385 170282337581078592166714789)
      ·
        refine ⟨31927938296452236031259023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170282337581078592166714789 31927938296452236031259023)
        ·
          refine ⟨47891907444678354046888535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31927938296452236031259023 47891907444678354046888535)
          ·
            refine ⟨71837861167017531070332803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47891907444678354046888535 71837861167017531070332803)
            ·
              refine ⟨107756791750526296605499205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71837861167017531070332803 107756791750526296605499205)
              ·
                refine ⟨20204398453223680613531101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107756791750526296605499205 20204398453223680613531101)
                ·
                  refine ⟨7576649419958880230074163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20204398453223680613531101 7576649419958880230074163)
                  ·
                    refine ⟨11364974129938320345111245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576649419958880230074163 11364974129938320345111245)
                    ·
                      refine ⟨4261865298726870129416717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11364974129938320345111245 4261865298726870129416717)
                      ·
                        rfl

theorem cell23_8299953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_8299953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299953 prefixEnd_8299953 := by exact prefixLift 8299953
  have htrace : WordTrace (prefixWord ++ tailWord_8299953) baseStart_8299953 baseEnd_8299953 := by
    simpa [prefixWord, tailWord_8299953, baseEnd_8299953] using wordTrace_append hprefix tailTrace_8299953
  have hstable : (prefixWord ++ tailWord_8299953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299953).length < 2 ^ (prefixWord ++ tailWord_8299953).sum := by decide
  have hdescent : baseEnd_8299953 < baseStart_8299953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299964 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_8299964 : Nat := 118140960795 + 8299964 * 2 ^ 59
def prefixEnd_8299964 : Nat := 4983230072969 + 3 ^ 40 * 8299964 * 2
def baseEnd_8299964 : Nat := 1420623649004689862126389

theorem tailTrace_8299964 : CollatzResearch.WordTrace tailWord_8299964 prefixEnd_8299964 1420623649004689862126389 := by
  unfold tailWord_8299964
  simp only [CollatzResearch.WordTrace]
  refine ⟨151362278451327711920849473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201816371268436949227799297 151362278451327711920849473)
  ·
    refine ⟨113521708838495783940637105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151362278451327711920849473 113521708838495783940637105)
    ·
      refine ⟨85141281628871837955477829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113521708838495783940637105 85141281628871837955477829)
      ·
        refine ⟨15963990305413469616652093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85141281628871837955477829 15963990305413469616652093)
        ·
          refine ⟨5986496364530051106244535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15963990305413469616652093 5986496364530051106244535)
          ·
            refine ⟨8979744546795076659366803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986496364530051106244535 8979744546795076659366803)
            ·
              refine ⟨13469616820192614989050205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8979744546795076659366803 13469616820192614989050205)
              ·
                refine ⟨5051106307572230620893827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13469616820192614989050205 5051106307572230620893827)
                ·
                  refine ⟨7576659461358345931340741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051106307572230620893827 7576659461358345931340741)
                  ·
                    refine ⟨1420623649004689862126389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7576659461358345931340741 1420623649004689862126389)
                    ·
                      rfl

theorem cell23_8299964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_8299964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299964 prefixEnd_8299964 := by exact prefixLift 8299964
  have htrace : WordTrace (prefixWord ++ tailWord_8299964) baseStart_8299964 baseEnd_8299964 := by
    simpa [prefixWord, tailWord_8299964, baseEnd_8299964] using wordTrace_append hprefix tailTrace_8299964
  have hstable : (prefixWord ++ tailWord_8299964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299964).length < 2 ^ (prefixWord ++ tailWord_8299964).sum := by decide
  have hdescent : baseEnd_8299964 < baseStart_8299964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8299980 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_8299980 : Nat := 118140960795 + 8299980 * 2 ^ 59
def prefixEnd_8299980 : Nat := 4983230072969 + 3 ^ 40 * 8299980 * 2
def baseEnd_8299980 : Nat := 4261879162704541523779093

theorem tailTrace_8299980 : CollatzResearch.WordTrace tailWord_8299980 prefixEnd_8299980 4261879162704541523779093 := by
  unfold tailWord_8299980
  simp only [CollatzResearch.WordTrace]
  refine ⟨151362570235298729287140697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201816760313731639049520929 151362570235298729287140697)
  ·
    refine ⟨113521927676474046965355523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151362570235298729287140697 113521927676474046965355523)
    ·
      refine ⟨170282891514711070448033285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113521927676474046965355523 170282891514711070448033285)
      ·
        refine ⟨31928042159008325709006241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170282891514711070448033285 31928042159008325709006241)
        ·
          refine ⟨23946031619256244281754681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31928042159008325709006241 23946031619256244281754681)
          ·
            refine ⟨17959523714442183211316011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23946031619256244281754681 17959523714442183211316011)
            ·
              refine ⟨26939285571663274816974017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959523714442183211316011 26939285571663274816974017)
              ·
                refine ⟨20204464178747456112730513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26939285571663274816974017 20204464178747456112730513)
                ·
                  refine ⟨15153348134060592084547885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20204464178747456112730513 15153348134060592084547885)
                  ·
                    refine ⟨5682505550272722031705457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15153348134060592084547885 5682505550272722031705457)
                    ·
                      refine ⟨4261879162704541523779093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682505550272722031705457 4261879162704541523779093)
                      ·
                        rfl

theorem cell23_8299980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_8299980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8299980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8299980 prefixEnd_8299980 := by exact prefixLift 8299980
  have htrace : WordTrace (prefixWord ++ tailWord_8299980) baseStart_8299980 baseEnd_8299980 := by
    simpa [prefixWord, tailWord_8299980, baseEnd_8299980] using wordTrace_append hprefix tailTrace_8299980
  have hstable : (prefixWord ++ tailWord_8299980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8299980).length < 2 ^ (prefixWord ++ tailWord_8299980).sum := by decide
  have hdescent : baseEnd_8299980 < baseStart_8299980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8299980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300038 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_8300038 : Nat := 118140960795 + 8300038 * 2 ^ 59
def prefixEnd_8300038 : Nat := 4983230072969 + 3 ^ 40 * 8300038 * 2
def baseEnd_8300038 : Nat := 4261908944582502296853827

theorem tailTrace_8300038 : CollatzResearch.WordTrace tailWord_8300038 prefixEnd_8300038 4261908944582502296853827 := by
  unfold tailWord_8300038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460226747012104202496649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201818170602924889653261845 9460226747012104202496649)
  ·
    refine ⟨7095170060259078151872487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9460226747012104202496649 7095170060259078151872487)
    ·
      refine ⟨10642755090388617227808731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095170060259078151872487 10642755090388617227808731)
      ·
        refine ⟨15964132635582925841713097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10642755090388617227808731 15964132635582925841713097)
        ·
          refine ⟨11973099476687194381284823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15964132635582925841713097 11973099476687194381284823)
          ·
            refine ⟨17959649215030791571927235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973099476687194381284823 17959649215030791571927235)
            ·
              refine ⟨26939473822546187357890853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959649215030791571927235 26939473822546187357890853)
              ·
                refine ⟨5051151341727410129604535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26939473822546187357890853 5051151341727410129604535)
                ·
                  refine ⟨7576727012591115194406803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051151341727410129604535 7576727012591115194406803)
                  ·
                    refine ⟨11365090518886672791610205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576727012591115194406803 11365090518886672791610205)
                    ·
                      refine ⟨4261908944582502296853827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365090518886672791610205 4261908944582502296853827)
                      ·
                        rfl

theorem cell23_8300038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_8300038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300038 prefixEnd_8300038 := by exact prefixLift 8300038
  have htrace : WordTrace (prefixWord ++ tailWord_8300038) baseStart_8300038 baseEnd_8300038 := by
    simpa [prefixWord, tailWord_8300038, baseEnd_8300038] using wordTrace_append hprefix tailTrace_8300038
  have hstable : (prefixWord ++ tailWord_8300038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300038).length < 2 ^ (prefixWord ++ tailWord_8300038).sum := by decide
  have hdescent : baseEnd_8300038 < baseStart_8300038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300044 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 1, 2, 2]
def baseStart_8300044 : Nat := 118140960795 + 8300044 * 2 ^ 59
def prefixEnd_8300044 : Nat := 4983230072969 + 3 ^ 40 * 8300044 * 2
def baseEnd_8300044 : Nat := 4261912025466429273378799

theorem tailTrace_8300044 : CollatzResearch.WordTrace tailWord_8300044 prefixEnd_8300044 4261912025466429273378799 := by
  unfold tailWord_8300044
  simp only [CollatzResearch.WordTrace]
  refine ⟨151363737371182798752305593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201818316494910398336407457 151363737371182798752305593)
  ·
    refine ⟨113522803028387099064229195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151363737371182798752305593 113522803028387099064229195)
    ·
      refine ⟨170284204542580648596343793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113522803028387099064229195 170284204542580648596343793)
      ·
        refine ⟨127713153406935486447257845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170284204542580648596343793 127713153406935486447257845)
        ·
          refine ⟨11973108131900201854430423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127713153406935486447257845 11973108131900201854430423)
          ·
            refine ⟨17959662197850302781645635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973108131900201854430423 17959662197850302781645635)
            ·
              refine ⟨26939493296775454172468453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959662197850302781645635 26939493296775454172468453)
              ·
                refine ⟨5051154993145397657337835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26939493296775454172468453 5051154993145397657337835)
                ·
                  refine ⟨7576732489718096486006753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051154993145397657337835 7576732489718096486006753)
                  ·
                    refine ⟨5682549367288572364505065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7576732489718096486006753 5682549367288572364505065)
                    ·
                      refine ⟨4261912025466429273378799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682549367288572364505065 4261912025466429273378799)
                      ·
                        rfl

theorem cell23_8300044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_8300044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300044 prefixEnd_8300044 := by exact prefixLift 8300044
  have htrace : WordTrace (prefixWord ++ tailWord_8300044) baseStart_8300044 baseEnd_8300044 := by
    simpa [prefixWord, tailWord_8300044, baseEnd_8300044] using wordTrace_append hprefix tailTrace_8300044
  have hstable : (prefixWord ++ tailWord_8300044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300044).length < 2 ^ (prefixWord ++ tailWord_8300044).sum := by decide
  have hdescent : baseEnd_8300044 < baseStart_8300044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300060 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_8300060 : Nat := 118140960795 + 8300060 * 2 ^ 59
def prefixEnd_8300060 : Nat := 4983230072969 + 3 ^ 40 * 8300060 * 2
def baseEnd_8300060 : Nat := 4261920241156901210778725

theorem tailTrace_8300060 : CollatzResearch.WordTrace tailWord_8300060 prefixEnd_8300060 4261920241156901210778725 := by
  unfold tailWord_8300060
  simp only [CollatzResearch.WordTrace]
  refine ⟨151364029155153816118596817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201818705540205088158129089 151364029155153816118596817)
  ·
    refine ⟨113523021866365362088947613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151364029155153816118596817 113523021866365362088947613)
    ·
      refine ⟨42571133199887010783355355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113523021866365362088947613 42571133199887010783355355)
      ·
        refine ⟨63856699799830516175033033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42571133199887010783355355 63856699799830516175033033)
        ·
          refine ⟨47892524849872887131274775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63856699799830516175033033 47892524849872887131274775)
          ·
            refine ⟨71838787274809330696912163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47892524849872887131274775 71838787274809330696912163)
            ·
              refine ⟨107758180912213996045368245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71838787274809330696912163 107758180912213996045368245)
              ·
                refine ⟨10102329460520062129253273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107758180912213996045368245 10102329460520062129253273)
                ·
                  refine ⟨7576747095390046596939955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102329460520062129253273 7576747095390046596939955)
                  ·
                    refine ⟨11365120643085069895409933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576747095390046596939955 11365120643085069895409933)
                    ·
                      refine ⟨4261920241156901210778725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365120643085069895409933 4261920241156901210778725)
                      ·
                        rfl

theorem cell23_8300060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_8300060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300060 prefixEnd_8300060 := by exact prefixLift 8300060
  have htrace : WordTrace (prefixWord ++ tailWord_8300060) baseStart_8300060 baseEnd_8300060 := by
    simpa [prefixWord, tailWord_8300060, baseEnd_8300060] using wordTrace_append hprefix tailTrace_8300060
  have hstable : (prefixWord ++ tailWord_8300060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300060).length < 2 ^ (prefixWord ++ tailWord_8300060).sum := by decide
  have hdescent : baseEnd_8300060 < baseStart_8300060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300087 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_8300087 : Nat := 118140960795 + 8300087 * 2 ^ 59
def prefixEnd_8300087 : Nat := 4983230072969 + 3 ^ 40 * 8300087 * 2
def baseEnd_8300087 : Nat := 4261934105134572605141101

theorem tailTrace_8300087 : CollatzResearch.WordTrace tailWord_8300087 prefixEnd_8300087 4261934105134572605141101 := by
  unfold tailWord_8300087
  simp only [CollatzResearch.WordTrace]
  refine ⟨302729043081209815848426515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201819362054139877232284343 302729043081209815848426515)
  ·
    refine ⟨454093564621814723772639773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302729043081209815848426515 454093564621814723772639773)
    ·
      refine ⟨170285086733180521414739915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454093564621814723772639773 170285086733180521414739915)
      ·
        refine ⟨255427630099770782122109873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170285086733180521414739915 255427630099770782122109873)
        ·
          refine ⟨191570722574828086591582405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255427630099770782122109873 191570722574828086591582405)
          ·
            refine ⟨35919510482780266235921701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191570722574828086591582405 35919510482780266235921701)
            ·
              refine ⟨6734908215521299919235319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35919510482780266235921701 6734908215521299919235319)
              ·
                refine ⟨10102362323281949878852979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734908215521299919235319 10102362323281949878852979)
                ·
                  refine ⟨15153543484922924818279469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10102362323281949878852979 15153543484922924818279469)
                  ·
                    refine ⟨5682578806846096806854801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15153543484922924818279469 5682578806846096806854801)
                    ·
                      refine ⟨4261934105134572605141101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682578806846096806854801 4261934105134572605141101)
                      ·
                        rfl

theorem cell23_8300087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_8300087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300087 prefixEnd_8300087 := by exact prefixLift 8300087
  have htrace : WordTrace (prefixWord ++ tailWord_8300087) baseStart_8300087 baseEnd_8300087 := by
    simpa [prefixWord, tailWord_8300087, baseEnd_8300087] using wordTrace_append hprefix tailTrace_8300087
  have hstable : (prefixWord ++ tailWord_8300087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300087).length < 2 ^ (prefixWord ++ tailWord_8300087).sum := by decide
  have hdescent : baseEnd_8300087 < baseStart_8300087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300143 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 7, 2]
def baseStart_8300143 : Nat := 118140960795 + 8300143 * 2 ^ 59
def prefixEnd_8300143 : Nat := 4983230072969 + 3 ^ 40 * 8300143 * 2
def baseEnd_8300143 : Nat := 4261962860051224386040843

theorem tailTrace_8300143 : CollatzResearch.WordTrace tailWord_8300143 prefixEnd_8300143 4261962860051224386040843 := by
  unfold tailWord_8300143
  simp only [CollatzResearch.WordTrace]
  refine ⟨302731085569006937412465083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201820723712671291608310055 302731085569006937412465083)
  ·
    refine ⟨454096628353510406118697625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302731085569006937412465083 454096628353510406118697625)
    ·
      refine ⟨340572471265132804589023219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454096628353510406118697625 340572471265132804589023219)
      ·
        refine ⟨510858706897699206883534829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340572471265132804589023219 510858706897699206883534829)
        ·
          refine ⟨191572015086637202581325561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510858706897699206883534829 191572015086637202581325561)
          ·
            refine ⟨143679011314977901935994171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191572015086637202581325561 143679011314977901935994171)
            ·
              refine ⟨215518516972466852903991257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143679011314977901935994171 215518516972466852903991257)
              ·
                refine ⟨161638887729350139677993443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215518516972466852903991257 161638887729350139677993443)
                ·
                  refine ⟨242458331594025209516990165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161638887729350139677993443 242458331594025209516990165)
                  ·
                    refine ⟨5682617146734965848054457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 242458331594025209516990165 5682617146734965848054457)
                    ·
                      refine ⟨4261962860051224386040843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682617146734965848054457 4261962860051224386040843)
                      ·
                        rfl

theorem cell23_8300143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 7, 2].length) (baseStart_8300143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300143 prefixEnd_8300143 := by exact prefixLift 8300143
  have htrace : WordTrace (prefixWord ++ tailWord_8300143) baseStart_8300143 baseEnd_8300143 := by
    simpa [prefixWord, tailWord_8300143, baseEnd_8300143] using wordTrace_append hprefix tailTrace_8300143
  have hstable : (prefixWord ++ tailWord_8300143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300143).length < 2 ^ (prefixWord ++ tailWord_8300143).sum := by decide
  have hdescent : baseEnd_8300143 < baseStart_8300143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300153 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_8300153 : Nat := 118140960795 + 8300153 * 2 ^ 59
def prefixEnd_8300153 : Nat := 4983230072969 + 3 ^ 40 * 8300153 * 2
def baseEnd_8300153 : Nat := 1420655998285923115638599

theorem tailTrace_8300153 : CollatzResearch.WordTrace tailWord_8300153 prefixEnd_8300153 1420655998285923115638599 := by
  unfold tailWord_8300153
  simp only [CollatzResearch.WordTrace]
  refine ⟨302731450298970709120329113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201820966865980472746886075 302731450298970709120329113)
  ·
    refine ⟨227048587724228031840246835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302731450298970709120329113 227048587724228031840246835)
    ·
      refine ⟨340572881586342047760370253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227048587724228031840246835 340572881586342047760370253)
      ·
        refine ⟨127714830594878267910138845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340572881586342047760370253 127714830594878267910138845)
        ·
          refine ⟨47893061473079350466302067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127714830594878267910138845 47893061473079350466302067)
          ·
            refine ⟨71839592209619025699453101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47893061473079350466302067 71839592209619025699453101)
            ·
              refine ⟨26939847078607134637294913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71839592209619025699453101 26939847078607134637294913)
              ·
                refine ⟨20204885308955350977971185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26939847078607134637294913 20204885308955350977971185)
                ·
                  refine ⟨15153663981716513233478389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20204885308955350977971185 15153663981716513233478389)
                  ·
                    refine ⟨1420655998285923115638599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15153663981716513233478389 1420655998285923115638599)
                    ·
                      rfl

theorem cell23_8300153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_8300153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300153 prefixEnd_8300153 := by exact prefixLift 8300153
  have htrace : WordTrace (prefixWord ++ tailWord_8300153) baseStart_8300153 baseEnd_8300153 := by
    simpa [prefixWord, tailWord_8300153, baseEnd_8300153] using wordTrace_append hprefix tailTrace_8300153
  have hstable : (prefixWord ++ tailWord_8300153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300153).length < 2 ^ (prefixWord ++ tailWord_8300153).sum := by decide
  have hdescent : baseEnd_8300153 < baseStart_8300153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300157 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 5]
def baseStart_8300157 : Nat := 118140960795 + 8300157 * 2 ^ 59
def prefixEnd_8300157 : Nat := 4983230072969 + 3 ^ 40 * 8300157 * 2
def baseEnd_8300157 : Nat := 473552227642265259029531

theorem tailTrace_8300157 : CollatzResearch.WordTrace tailWord_8300157 prefixEnd_8300157 473552227642265259029531 := by
  unfold tailWord_8300157
  simp only [CollatzResearch.WordTrace]
  refine ⟨302731596190956217803474725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201821064127304145202316483 302731596190956217803474725)
  ·
    refine ⟨56762174285804290838151511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302731596190956217803474725 56762174285804290838151511)
    ·
      refine ⟨85143261428706436257227267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56762174285804290838151511 85143261428706436257227267)
      ·
        refine ⟨127714892143059654385840901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85143261428706436257227267 127714892143059654385840901)
        ·
          refine ⟨23946542276823685197345169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127714892143059654385840901 23946542276823685197345169)
          ·
            refine ⟨17959906707617763898008877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23946542276823685197345169 17959906707617763898008877)
            ·
              refine ⟨6734965015356661461753329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17959906707617763898008877 6734965015356661461753329)
              ·
                refine ⟨5051223761517496096314997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734965015356661461753329 5051223761517496096314997)
                ·
                  refine ⟨473552227642265259029531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5051223761517496096314997 473552227642265259029531)
                  ·
                    rfl

theorem cell23_8300157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_8300157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300157 prefixEnd_8300157 := by exact prefixLift 8300157
  have htrace : WordTrace (prefixWord ++ tailWord_8300157) baseStart_8300157 baseEnd_8300157 := by
    simpa [prefixWord, tailWord_8300157, baseEnd_8300157] using wordTrace_append hprefix tailTrace_8300157
  have hstable : (prefixWord ++ tailWord_8300157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300157).length < 2 ^ (prefixWord ++ tailWord_8300157).sum := by decide
  have hdescent : baseEnd_8300157 < baseStart_8300157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300168 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_8300168 : Nat := 118140960795 + 8300168 * 2 ^ 59
def prefixEnd_8300168 : Nat := 4983230072969 + 3 ^ 40 * 8300168 * 2
def baseEnd_8300168 : Nat := 4261975697067586788228229

theorem tailTrace_8300168 : CollatzResearch.WordTrace tailWord_8300168 prefixEnd_8300168 4261975697067586788228229 := by
  unfold tailWord_8300168
  simp only [CollatzResearch.WordTrace]
  refine ⟨151365998696958183341062579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201821331595944244454750105 151365998696958183341062579)
  ·
    refine ⟨227048998045437275011593869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151365998696958183341062579 227048998045437275011593869)
    ·
      refine ⟨85143374267038978129347701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227048998045437275011593869 85143374267038978129347701)
      ·
        refine ⟨7982191337534904199626347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85143374267038978129347701 7982191337534904199626347)
        ·
          refine ⟨11973287006302356299439521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982191337534904199626347 11973287006302356299439521)
          ·
            refine ⟨8979965254726767224579641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11973287006302356299439521 8979965254726767224579641)
            ·
              refine ⟨6734973941045075418434731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979965254726767224579641 6734973941045075418434731)
              ·
                refine ⟨10102460911567613127652097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734973941045075418434731 10102460911567613127652097)
                ·
                  refine ⟨7576845683675709845739073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102460911567613127652097 7576845683675709845739073)
                  ·
                    refine ⟨5682634262756782384304305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7576845683675709845739073 5682634262756782384304305)
                    ·
                      refine ⟨4261975697067586788228229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682634262756782384304305 4261975697067586788228229)
                      ·
                        rfl

theorem cell23_8300168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_8300168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300168 prefixEnd_8300168 := by exact prefixLift 8300168
  have htrace : WordTrace (prefixWord ++ tailWord_8300168) baseStart_8300168 baseEnd_8300168 := by
    simpa [prefixWord, tailWord_8300168, baseEnd_8300168] using wordTrace_append hprefix tailTrace_8300168
  have hstable : (prefixWord ++ tailWord_8300168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300168).length < 2 ^ (prefixWord ++ tailWord_8300168).sum := by decide
  have hdescent : baseEnd_8300168 < baseStart_8300168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300176 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_8300176 : Nat := 118140960795 + 8300176 * 2 ^ 59
def prefixEnd_8300176 : Nat := 4983230072969 + 3 ^ 40 * 8300176 * 2
def baseEnd_8300176 : Nat := 4261979804912822756928191

theorem tailTrace_8300176 : CollatzResearch.WordTrace tailWord_8300176 prefixEnd_8300176 4261979804912822756928191 := by
  unfold tailWord_8300176
  simp only [CollatzResearch.WordTrace]
  refine ⟨151366144588943692024208191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201821526118591589365610921 151366144588943692024208191)
  ·
    refine ⟨227049216883415538036312287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151366144588943692024208191 227049216883415538036312287)
    ·
      refine ⟨340573825325123307054468431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227049216883415538036312287 340573825325123307054468431)
      ·
        refine ⟨510860737987684960581702647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340573825325123307054468431 510860737987684960581702647)
        ·
          refine ⟨766291106981527440872553971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510860737987684960581702647 766291106981527440872553971)
          ·
            refine ⟨1149436660472291161308830957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766291106981527440872553971 1149436660472291161308830957)
            ·
              refine ⟨431038747677109185490811609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1149436660472291161308830957 431038747677109185490811609)
              ·
                refine ⟨323279060757831889118108707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431038747677109185490811609 323279060757831889118108707)
                ·
                  refine ⟨484918591136747833677163061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323279060757831889118108707 484918591136747833677163061)
                  ·
                    refine ⟨45461117919070109407234037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484918591136747833677163061 45461117919070109407234037)
                    ·
                      refine ⟨4261979804912822756928191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45461117919070109407234037 4261979804912822756928191)
                      ·
                        rfl

theorem cell23_8300176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_8300176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300176 prefixEnd_8300176 := by exact prefixLift 8300176
  have htrace : WordTrace (prefixWord ++ tailWord_8300176) baseStart_8300176 baseEnd_8300176 := by
    simpa [prefixWord, tailWord_8300176, baseEnd_8300176] using wordTrace_append hprefix tailTrace_8300176
  have hstable : (prefixWord ++ tailWord_8300176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300176).length < 2 ^ (prefixWord ++ tailWord_8300176).sum := by decide
  have hdescent : baseEnd_8300176 < baseStart_8300176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300210 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_8300210 : Nat := 118140960795 + 8300210 * 2 ^ 59
def prefixEnd_8300210 : Nat := 4983230072969 + 3 ^ 40 * 8300210 * 2
def baseEnd_8300210 : Nat := 4261997263255075623903035

theorem tailTrace_8300210 : CollatzResearch.WordTrace tailWord_8300210 prefixEnd_8300210 4261997263255075623903035 := by
  unfold tailWord_8300210
  simp only [CollatzResearch.WordTrace]
  refine ⟨75683382314941051963788521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201822352839842805236769389 75683382314941051963788521)
  ·
    refine ⟨56762536736205788972841391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75683382314941051963788521 56762536736205788972841391)
    ·
      refine ⟨85143805104308683459262087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56762536736205788972841391 85143805104308683459262087)
      ·
        refine ⟨127715707656463025188893131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85143805104308683459262087 127715707656463025188893131)
        ·
          refine ⟨191573561484694537783339697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127715707656463025188893131 191573561484694537783339697)
          ·
            refine ⟨143680171113520903337504773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191573561484694537783339697 143680171113520903337504773)
            ·
              refine ⟨26940032083785169375782145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143680171113520903337504773 26940032083785169375782145)
              ·
                refine ⟨20205024062838877031836609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26940032083785169375782145 20205024062838877031836609)
                ·
                  refine ⟨15153768047129157773877457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20205024062838877031836609 15153768047129157773877457)
                  ·
                    refine ⟨11365326035346868330408093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15153768047129157773877457 11365326035346868330408093)
                    ·
                      refine ⟨4261997263255075623903035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365326035346868330408093 4261997263255075623903035)
                      ·
                        rfl

theorem cell23_8300210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_8300210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300210 prefixEnd_8300210 := by exact prefixLift 8300210
  have htrace : WordTrace (prefixWord ++ tailWord_8300210) baseStart_8300210 baseEnd_8300210 := by
    simpa [prefixWord, tailWord_8300210, baseEnd_8300210] using wordTrace_append hprefix tailTrace_8300210
  have hstable : (prefixWord ++ tailWord_8300210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300210).length < 2 ^ (prefixWord ++ tailWord_8300210).sum := by decide
  have hdescent : baseEnd_8300210 < baseStart_8300210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300244 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_8300244 : Nat := 118140960795 + 8300244 * 2 ^ 59
def prefixEnd_8300244 : Nat := 4983230072969 + 3 ^ 40 * 8300244 * 2
def baseEnd_8300244 : Nat := 4262014721597328490877879

theorem tailTrace_8300244 : CollatzResearch.WordTrace tailWord_8300244 prefixEnd_8300244 4262014721597328490877879 := by
  unfold tailWord_8300244
  simp only [CollatzResearch.WordTrace]
  refine ⟨151367384670820515830945893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201823179561094021107927857 151367384670820515830945893)
  ·
    refine ⟨28381384625778846718302355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151367384670820515830945893 28381384625778846718302355)
    ·
      refine ⟨42572076938668270077453533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28381384625778846718302355 42572076938668270077453533)
      ·
        refine ⟨15964528852000601279045075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42572076938668270077453533 15964528852000601279045075)
        ·
          refine ⟨23946793278000901918567613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15964528852000601279045075 23946793278000901918567613)
          ·
            refine ⟨8980047479250338219462855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23946793278000901918567613 8980047479250338219462855)
            ·
              refine ⟨13470071218875507329194283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8980047479250338219462855 13470071218875507329194283)
              ·
                refine ⟨20205106828313260993791425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13470071218875507329194283 20205106828313260993791425)
                ·
                  refine ⟨15153830121234945745343569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20205106828313260993791425 15153830121234945745343569)
                  ·
                    refine ⟨11365372590926209309007677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15153830121234945745343569 11365372590926209309007677)
                    ·
                      refine ⟨4262014721597328490877879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365372590926209309007677 4262014721597328490877879)
                      ·
                        rfl

theorem cell23_8300244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_8300244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300244 prefixEnd_8300244 := by exact prefixLift 8300244
  have htrace : WordTrace (prefixWord ++ tailWord_8300244) baseStart_8300244 baseEnd_8300244 := by
    simpa [prefixWord, tailWord_8300244, baseEnd_8300244] using wordTrace_append hprefix tailTrace_8300244
  have hstable : (prefixWord ++ tailWord_8300244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300244).length < 2 ^ (prefixWord ++ tailWord_8300244).sum := by decide
  have hdescent : baseEnd_8300244 < baseStart_8300244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300260 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_8300260 : Nat := 118140960795 + 8300260 * 2 ^ 59
def prefixEnd_8300260 : Nat := 4983230072969 + 3 ^ 40 * 8300260 * 2
def baseEnd_8300260 : Nat := 1420674312429266809425935

theorem tailTrace_8300260 : CollatzResearch.WordTrace tailWord_8300260 prefixEnd_8300260 1420674312429266809425935 := by
  unfold tailWord_8300260
  simp only [CollatzResearch.WordTrace]
  refine ⟨151367676454791533197237117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201823568606388710929649489 151367676454791533197237117)
  ·
    refine ⟨56762878670546824948963919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151367676454791533197237117 56762878670546824948963919)
    ·
      refine ⟨85144318005820237423445879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56762878670546824948963919 85144318005820237423445879)
      ·
        refine ⟨127716477008730356135168819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85144318005820237423445879 127716477008730356135168819)
        ·
          refine ⟨191574715513095534202753229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127716477008730356135168819 191574715513095534202753229)
          ·
            refine ⟨71840518317410825326032461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191574715513095534202753229 71840518317410825326032461)
            ·
              refine ⟨26940194369029059497262173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71840518317410825326032461 26940194369029059497262173)
              ·
                refine ⟨10102572888385897311473315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26940194369029059497262173 10102572888385897311473315)
                ·
                  refine ⟨15153859332578845967209973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10102572888385897311473315 15153859332578845967209973)
                  ·
                    refine ⟨1420674312429266809425935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15153859332578845967209973 1420674312429266809425935)
                    ·
                      rfl

theorem cell23_8300260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_8300260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300260 prefixEnd_8300260 := by exact prefixLift 8300260
  have htrace : WordTrace (prefixWord ++ tailWord_8300260) baseStart_8300260 baseEnd_8300260 := by
    simpa [prefixWord, tailWord_8300260, baseEnd_8300260] using wordTrace_append hprefix tailTrace_8300260
  have hstable : (prefixWord ++ tailWord_8300260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300260).length < 2 ^ (prefixWord ++ tailWord_8300260).sum := by decide
  have hdescent : baseEnd_8300260 < baseStart_8300260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300274 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_8300274 : Nat := 118140960795 + 8300274 * 2 ^ 59
def prefixEnd_8300274 : Nat := 4983230072969 + 3 ^ 40 * 8300274 * 2
def baseEnd_8300274 : Nat := 4262030126016963373502741

theorem tailTrace_8300274 : CollatzResearch.WordTrace tailWord_8300274 prefixEnd_8300274 4262030126016963373502741 := by
  unfold tailWord_8300274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75683965882883086696370969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201823909021021564523655917 75683965882883086696370969)
  ·
    refine ⟨56762974412162315022278227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75683965882883086696370969 56762974412162315022278227)
    ·
      refine ⟨85144461618243472533417341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56762974412162315022278227 85144461618243472533417341)
      ·
        refine ⟨31929173106841302200031503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85144461618243472533417341 31929173106841302200031503)
        ·
          refine ⟨47893759660261953300047255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31929173106841302200031503 47893759660261953300047255)
          ·
            refine ⟨71840639490392929950070883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47893759660261953300047255 71840639490392929950070883)
            ·
              refine ⟨107760959235589394925106325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71840639490392929950070883 107760959235589394925106325)
              ·
                refine ⟨5051294964168252887114359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107760959235589394925106325 5051294964168252887114359)
                ·
                  refine ⟨7576942446252379330671539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051294964168252887114359 7576942446252379330671539)
                  ·
                    refine ⟨11365413669378568996007309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576942446252379330671539 11365413669378568996007309)
                    ·
                      refine ⟨4262030126016963373502741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365413669378568996007309 4262030126016963373502741)
                      ·
                        rfl

theorem cell23_8300274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_8300274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300274 prefixEnd_8300274 := by exact prefixLift 8300274
  have htrace : WordTrace (prefixWord ++ tailWord_8300274) baseStart_8300274 baseEnd_8300274 := by
    simpa [prefixWord, tailWord_8300274, baseEnd_8300274] using wordTrace_append hprefix tailTrace_8300274
  have hstable : (prefixWord ++ tailWord_8300274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300274).length < 2 ^ (prefixWord ++ tailWord_8300274).sum := by decide
  have hdescent : baseEnd_8300274 < baseStart_8300274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3]
def baseStart_8300283 : Nat := 118140960795 + 8300283 * 2 ^ 59
def prefixEnd_8300283 : Nat := 4983230072969 + 3 ^ 40 * 8300283 * 2
def baseEnd_8300283 : Nat := 4262034747342853838290199

theorem tailTrace_8300283 : CollatzResearch.WordTrace tailWord_8300283 prefixEnd_8300283 4262034747342853838290199 := by
  unfold tailWord_8300283
  simp only [CollatzResearch.WordTrace]
  refine ⟨302736191788499741322561503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201824127858999827548374335 302736191788499741322561503)
  ·
    refine ⟨454104287682749611983842255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302736191788499741322561503 454104287682749611983842255)
    ·
      refine ⟨681156431524124417975763383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454104287682749611983842255 681156431524124417975763383)
      ·
        refine ⟨1021734647286186626963645075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681156431524124417975763383 1021734647286186626963645075)
        ·
          refine ⟨1532601970929279940445467613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021734647286186626963645075 1532601970929279940445467613)
          ·
            refine ⟨574725739098479977667050355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1532601970929279940445467613 574725739098479977667050355)
            ·
              refine ⟨862088608647719966500575533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574725739098479977667050355 862088608647719966500575533)
              ·
                refine ⟨323283228242894987437715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862088608647719966500575533 323283228242894987437715825)
                ·
                  refine ⟨242462421182171240578286869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323283228242894987437715825 242462421182171240578286869)
                  ·
                    refine ⟨11365425992914276902107197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242462421182171240578286869 11365425992914276902107197)
                    ·
                      refine ⟨4262034747342853838290199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365425992914276902107197 4262034747342853838290199)
                      ·
                        rfl

theorem cell23_8300283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3].length) (baseStart_8300283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300283 prefixEnd_8300283 := by exact prefixLift 8300283
  have htrace : WordTrace (prefixWord ++ tailWord_8300283) baseStart_8300283 baseEnd_8300283 := by
    simpa [prefixWord, tailWord_8300283, baseEnd_8300283] using wordTrace_append hprefix tailTrace_8300283
  have hstable : (prefixWord ++ tailWord_8300283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300283).length < 2 ^ (prefixWord ++ tailWord_8300283).sum := by decide
  have hdescent : baseEnd_8300283 < baseStart_8300283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300300 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_8300300 : Nat := 118140960795 + 8300300 * 2 ^ 59
def prefixEnd_8300300 : Nat := 4983230072969 + 3 ^ 40 * 8300300 * 2
def baseEnd_8300300 : Nat := 4262043476513980271777621

theorem tailTrace_8300300 : CollatzResearch.WordTrace tailWord_8300300 prefixEnd_8300300 4262043476513980271777621 := by
  unfold tailWord_8300300
  simp only [CollatzResearch.WordTrace]
  refine ⟨151368405914719076612965177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201824541219625435483953569 151368405914719076612965177)
  ·
    refine ⟨113526304436039307459723883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151368405914719076612965177 113526304436039307459723883)
    ·
      refine ⟨170289456654058961189585825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113526304436039307459723883 170289456654058961189585825)
      ·
        refine ⟨127717092490544220892189369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170289456654058961189585825 127717092490544220892189369)
        ·
          refine ⟨95787819367908165669142027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127717092490544220892189369 95787819367908165669142027)
          ·
            refine ⟨143681729051862248503713041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95787819367908165669142027 143681729051862248503713041)
            ·
              refine ⟨107761296788896686377784781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143681729051862248503713041 107761296788896686377784781)
              ·
                refine ⟨40410486295836257391669293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107761296788896686377784781 40410486295836257391669293)
                ·
                  refine ⟨15153932360938596521875985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40410486295836257391669293 15153932360938596521875985)
                  ·
                    refine ⟨11365449270703947391406989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15153932360938596521875985 11365449270703947391406989)
                    ·
                      refine ⟨4262043476513980271777621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365449270703947391406989 4262043476513980271777621)
                      ·
                        rfl

theorem cell23_8300300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_8300300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300300 prefixEnd_8300300 := by exact prefixLift 8300300
  have htrace : WordTrace (prefixWord ++ tailWord_8300300) baseStart_8300300 baseEnd_8300300 := by
    simpa [prefixWord, tailWord_8300300, baseEnd_8300300] using wordTrace_append hprefix tailTrace_8300300
  have hstable : (prefixWord ++ tailWord_8300300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300300).length < 2 ^ (prefixWord ++ tailWord_8300300).sum := by decide
  have hdescent : baseEnd_8300300 < baseStart_8300300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300318 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_8300318 : Nat := 118140960795 + 8300318 * 2 ^ 59
def prefixEnd_8300318 : Nat := 4983230072969 + 3 ^ 40 * 8300318 * 2
def baseEnd_8300318 : Nat := 4262052719165761201352539

theorem tailTrace_8300318 : CollatzResearch.WordTrace tailWord_8300318 prefixEnd_8300318 4262052719165761201352539 := by
  unfold tailWord_8300318
  simp only [CollatzResearch.WordTrace]
  refine ⟨37842183542921617787510701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201824978895581961533390405 37842183542921617787510701)
  ·
    refine ⟨14190818828595606670316513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37842183542921617787510701 14190818828595606670316513)
    ·
      refine ⟨10643114121446705002737385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14190818828595606670316513 10643114121446705002737385)
      ·
        refine ⟨7982335591085028752053039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10643114121446705002737385 7982335591085028752053039)
        ·
          refine ⟨11973503386627543128079559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982335591085028752053039 11973503386627543128079559)
          ·
            refine ⟨17960255079941314692119339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973503386627543128079559 17960255079941314692119339)
            ·
              refine ⟨26940382619911972038179009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17960255079941314692119339 26940382619911972038179009)
              ·
                refine ⟨20205286964933979028634257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26940382619911972038179009 20205286964933979028634257)
                ·
                  refine ⟨15153965223700484271475693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20205286964933979028634257 15153965223700484271475693)
                  ·
                    refine ⟨5682736958887681601803385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15153965223700484271475693 5682736958887681601803385)
                    ·
                      refine ⟨4262052719165761201352539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682736958887681601803385 4262052719165761201352539)
                      ·
                        rfl

theorem cell23_8300318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_8300318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300318 prefixEnd_8300318 := by exact prefixLift 8300318
  have htrace : WordTrace (prefixWord ++ tailWord_8300318) baseStart_8300318 baseEnd_8300318 := by
    simpa [prefixWord, tailWord_8300318, baseEnd_8300318] using wordTrace_append hprefix tailTrace_8300318
  have hstable : (prefixWord ++ tailWord_8300318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300318).length < 2 ^ (prefixWord ++ tailWord_8300318).sum := by decide
  have hdescent : baseEnd_8300318 < baseStart_8300318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300341 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_8300341 : Nat := 118140960795 + 8300341 * 2 ^ 59
def prefixEnd_8300341 : Nat := 4983230072969 + 3 ^ 40 * 8300341 * 2
def baseEnd_8300341 : Nat := 1420688176406938203788311

theorem tailTrace_8300341 : CollatzResearch.WordTrace tailWord_8300341 prefixEnd_8300341 1420688176406938203788311 := by
  unfold tailWord_8300341
  simp only [CollatzResearch.WordTrace]
  refine ⟨302738307222289617228172877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201825538148193078152115251 302738307222289617228172877)
  ·
    refine ⟨113526865208358606460564829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302738307222289617228172877 113526865208358606460564829)
    ·
      refine ⟨42572574453134477422711811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113526865208358606460564829 42572574453134477422711811)
      ·
        refine ⟨63858861679701716134067717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42572574453134477422711811 63858861679701716134067717)
        ·
          refine ⟨11973536564944071775137697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63858861679701716134067717 11973536564944071775137697)
          ·
            refine ⟨8980152423708053831353273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11973536564944071775137697 8980152423708053831353273)
            ·
              refine ⟨6735114317781040373514955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8980152423708053831353273 6735114317781040373514955)
              ·
                refine ⟨10102671476671560560272433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735114317781040373514955 10102671476671560560272433)
                ·
                  refine ⟨7577003607503670420204325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102671476671560560272433 7577003607503670420204325)
                  ·
                    refine ⟨1420688176406938203788311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577003607503670420204325 1420688176406938203788311)
                    ·
                      rfl

theorem cell23_8300341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_8300341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300341 prefixEnd_8300341 := by exact prefixLift 8300341
  have htrace : WordTrace (prefixWord ++ tailWord_8300341) baseStart_8300341 baseEnd_8300341 := by
    simpa [prefixWord, tailWord_8300341, baseEnd_8300341] using wordTrace_append hprefix tailTrace_8300341
  have hstable : (prefixWord ++ tailWord_8300341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300341).length < 2 ^ (prefixWord ++ tailWord_8300341).sum := by decide
  have hdescent : baseEnd_8300341 < baseStart_8300341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300343 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_8300343 : Nat := 118140960795 + 8300343 * 2 ^ 59
def prefixEnd_8300343 : Nat := 4983230072969 + 3 ^ 40 * 8300343 * 2
def baseEnd_8300343 : Nat := 4262065556182123603539923

theorem tailTrace_8300343 : CollatzResearch.WordTrace tailWord_8300343 prefixEnd_8300343 4262065556182123603539923 := by
  unfold tailWord_8300343
  simp only [CollatzResearch.WordTrace]
  refine ⟨302738380168282371569745683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201825586778854914379830455 302738380168282371569745683)
  ·
    refine ⟨454107570252423557354618525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302738380168282371569745683 454107570252423557354618525)
    ·
      refine ⟨170290338844658834007981947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454107570252423557354618525 170290338844658834007981947)
      ·
        refine ⟨255435508266988251011972921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170290338844658834007981947 255435508266988251011972921)
        ·
          refine ⟨191576631200241188258979691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255435508266988251011972921 191576631200241188258979691)
          ·
            refine ⟨287364946800361782388469537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191576631200241188258979691 287364946800361782388469537)
            ·
              refine ⟨215523710100271336791352153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287364946800361782388469537 215523710100271336791352153)
              ·
                refine ⟨161642782575203502593514115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215523710100271336791352153 161642782575203502593514115)
                ·
                  refine ⟨242464173862805253890271173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161642782575203502593514115 242464173862805253890271173)
                  ·
                    refine ⟨45462032599275985104425845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242464173862805253890271173 45462032599275985104425845)
                    ·
                      refine ⟨4262065556182123603539923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45462032599275985104425845 4262065556182123603539923)
                      ·
                        rfl

theorem cell23_8300343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_8300343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300343 prefixEnd_8300343 := by exact prefixLift 8300343
  have htrace : WordTrace (prefixWord ++ tailWord_8300343) baseStart_8300343 baseEnd_8300343 := by
    simpa [prefixWord, tailWord_8300343, baseEnd_8300343] using wordTrace_append hprefix tailTrace_8300343
  have hstable : (prefixWord ++ tailWord_8300343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300343).length < 2 ^ (prefixWord ++ tailWord_8300343).sum := by decide
  have hdescent : baseEnd_8300343 < baseStart_8300343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300351 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 1, 2, 3]
def baseStart_8300351 : Nat := 118140960795 + 8300351 * 2 ^ 59
def prefixEnd_8300351 : Nat := 4983230072969 + 3 ^ 40 * 8300351 * 2
def baseEnd_8300351 : Nat := 4262069664027359572239887

theorem tailTrace_8300351 : CollatzResearch.WordTrace tailWord_8300351 prefixEnd_8300351 4262069664027359572239887 := by
  unfold tailWord_8300351
  simp only [CollatzResearch.WordTrace]
  refine ⟨302738671952253388936036907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201825781301502259290691271 302738671952253388936036907)
  ·
    refine ⟨454108007928380083404055361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302738671952253388936036907 454108007928380083404055361)
    ·
      refine ⟨340581005946285062553041521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454108007928380083404055361 340581005946285062553041521)
      ·
        refine ⟨255435754459713796914781141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340581005946285062553041521 255435754459713796914781141)
        ·
          refine ⟨5986775495149542115190183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 255435754459713796914781141 5986775495149542115190183)
          ·
            refine ⟨8980163242724313172785275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986775495149542115190183 8980163242724313172785275)
            ·
              refine ⟨13470244864086469759177913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8980163242724313172785275 13470244864086469759177913)
              ·
                refine ⟨10102683648064852319383435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13470244864086469759177913 10102683648064852319383435)
                ·
                  refine ⟨15154025472097278479075153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10102683648064852319383435 15154025472097278479075153)
                  ·
                    refine ⟨11365519104072958859306365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15154025472097278479075153 11365519104072958859306365)
                    ·
                      refine ⟨4262069664027359572239887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11365519104072958859306365 4262069664027359572239887)
                      ·
                        rfl

theorem cell23_8300351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_8300351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300351 prefixEnd_8300351 := by exact prefixLift 8300351
  have htrace : WordTrace (prefixWord ++ tailWord_8300351) baseStart_8300351 baseEnd_8300351 := by
    simpa [prefixWord, tailWord_8300351, baseEnd_8300351] using wordTrace_append hprefix tailTrace_8300351
  have hstable : (prefixWord ++ tailWord_8300351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300351).length < 2 ^ (prefixWord ++ tailWord_8300351).sum := by decide
  have hdescent : baseEnd_8300351 < baseStart_8300351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300357 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_8300357 : Nat := 118140960795 + 8300357 * 2 ^ 59
def prefixEnd_8300357 : Nat := 4983230072969 + 3 ^ 40 * 8300357 * 2
def baseEnd_8300357 : Nat := 4262072744911286548764859

theorem tailTrace_8300357 : CollatzResearch.WordTrace tailWord_8300357 prefixEnd_8300357 4262072744911286548764859 := by
  unfold tailWord_8300357
  simp only [CollatzResearch.WordTrace]
  refine ⟨302738890790231651960755325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201825927193487767973836883 302738890790231651960755325)
  ·
    refine ⟨113527084046336869485283247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302738890790231651960755325 113527084046336869485283247)
    ·
      refine ⟨170290626069505304227924871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113527084046336869485283247 170290626069505304227924871)
      ·
        refine ⟨255435939104257956341887307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170290626069505304227924871 255435939104257956341887307)
        ·
          refine ⟨383153908656386934512830961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255435939104257956341887307 383153908656386934512830961)
          ·
            refine ⟨287365431492290200884623221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383153908656386934512830961 287365431492290200884623221)
            ·
              refine ⟨26940509202402206332933427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287365431492290200884623221 26940509202402206332933427)
              ·
                refine ⟨40410763803603309499400141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26940509202402206332933427 40410763803603309499400141)
                ·
                  refine ⟨15154036426351241062275053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40410763803603309499400141 15154036426351241062275053)
                  ·
                    refine ⟨5682763659881715398353145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15154036426351241062275053 5682763659881715398353145)
                    ·
                      refine ⟨4262072744911286548764859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682763659881715398353145 4262072744911286548764859)
                      ·
                        rfl

theorem cell23_8300357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_8300357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300357 prefixEnd_8300357 := by exact prefixLift 8300357
  have htrace : WordTrace (prefixWord ++ tailWord_8300357) baseStart_8300357 baseEnd_8300357 := by
    simpa [prefixWord, tailWord_8300357, baseEnd_8300357] using wordTrace_append hprefix tailTrace_8300357
  have hstable : (prefixWord ++ tailWord_8300357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300357).length < 2 ^ (prefixWord ++ tailWord_8300357).sum := by decide
  have hdescent : baseEnd_8300357 < baseStart_8300357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300393 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 11]
def baseStart_8300393 : Nat := 118140960795 + 8300393 * 2 ^ 59
def prefixEnd_8300393 : Nat := 4983230072969 + 3 ^ 40 * 8300393 * 2
def baseEnd_8300393 : Nat := 473565692246094267546077

theorem tailTrace_8300393 : CollatzResearch.WordTrace tailWord_8300393 prefixEnd_8300393 473565692246094267546077 := by
  unfold tailWord_8300393
  simp only [CollatzResearch.WordTrace]
  refine ⟨302740203818101230109065833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201826802545400820072710555 302740203818101230109065833)
  ·
    refine ⟨227055152863575922581799375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302740203818101230109065833 227055152863575922581799375)
    ·
      refine ⟨340582729295363883872699063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227055152863575922581799375 340582729295363883872699063)
      ·
        refine ⟨510874093943045825809048595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340582729295363883872699063 510874093943045825809048595)
        ·
          refine ⟨766311140914568738713572893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510874093943045825809048595 766311140914568738713572893)
          ·
            refine ⟨287366677842963277017589835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766311140914568738713572893 287366677842963277017589835)
            ·
              refine ⟨431050016764444915526384753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287366677842963277017589835 431050016764444915526384753)
              ·
                refine ⟨323287512573333686644788565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431050016764444915526384753 323287512573333686644788565)
                ·
                  refine ⟨473565692246094267546077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 323287512573333686644788565 473565692246094267546077)
                  ·
                    rfl

theorem cell23_8300393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_8300393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300393 prefixEnd_8300393 := by exact prefixLift 8300393
  have htrace : WordTrace (prefixWord ++ tailWord_8300393) baseStart_8300393 baseEnd_8300393 := by
    simpa [prefixWord, tailWord_8300393, baseEnd_8300393] using wordTrace_append hprefix tailTrace_8300393
  have hstable : (prefixWord ++ tailWord_8300393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300393).length < 2 ^ (prefixWord ++ tailWord_8300393).sum := by decide
  have hdescent : baseEnd_8300393 < baseStart_8300393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300444 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 5]
def baseStart_8300444 : Nat := 118140960795 + 8300444 * 2 ^ 59
def prefixEnd_8300444 : Nat := 4983230072969 + 3 ^ 40 * 8300444 * 2
def baseEnd_8300444 : Nat := 473568601969803078708551

theorem tailTrace_8300444 : CollatzResearch.WordTrace tailWord_8300444 prefixEnd_8300444 473568601969803078708551 := by
  unfold tailWord_8300444
  simp only [CollatzResearch.WordTrace]
  refine ⟨151371031970458232909586193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201828042627277643879448257 151371031970458232909586193)
  ·
    refine ⟨113528273977843674682189645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151371031970458232909586193 113528273977843674682189645)
    ·
      refine ⟨42573102741691378005821117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113528273977843674682189645 42573102741691378005821117)
      ·
        refine ⟨15964913528134266752182919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42573102741691378005821117 15964913528134266752182919)
        ·
          refine ⟨23947370292201400128274379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15964913528134266752182919 23947370292201400128274379)
          ·
            refine ⟨35921055438302100192411569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23947370292201400128274379 35921055438302100192411569)
            ·
              refine ⟨26940791578726575144308677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35921055438302100192411569 26940791578726575144308677)
              ·
                refine ⟨5051398421011232839557877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26940791578726575144308677 5051398421011232839557877)
                ·
                  refine ⟨473568601969803078708551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5051398421011232839557877 473568601969803078708551)
                  ·
                    rfl

theorem cell23_8300444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_8300444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300444 prefixEnd_8300444 := by exact prefixLift 8300444
  have htrace : WordTrace (prefixWord ++ tailWord_8300444) baseStart_8300444 baseEnd_8300444 := by
    simpa [prefixWord, tailWord_8300444, baseEnd_8300444] using wordTrace_append hprefix tailTrace_8300444
  have hstable : (prefixWord ++ tailWord_8300444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300444).length < 2 ^ (prefixWord ++ tailWord_8300444).sum := by decide
  have hdescent : baseEnd_8300444 < baseStart_8300444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300477 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_8300477 : Nat := 118140960795 + 8300477 * 2 ^ 59
def prefixEnd_8300477 : Nat := 4983230072969 + 3 ^ 40 * 8300477 * 2
def baseEnd_8300477 : Nat := 4262134362589826079264307

theorem tailTrace_8300477 : CollatzResearch.WordTrace tailWord_8300477 prefixEnd_8300477 4262134362589826079264307 := by
  unfold tailWord_8300477
  simp only [CollatzResearch.WordTrace]
  refine ⟨302743267549796912455123685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201828845033197941636749123 302743267549796912455123685)
  ·
    refine ⟨56764362665586921085335691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302743267549796912455123685 56764362665586921085335691)
    ·
      refine ⟨85146543998380381628003537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56764362665586921085335691 85146543998380381628003537)
      ·
        refine ⟨63859907998785286221002653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85146543998380381628003537 63859907998785286221002653)
        ·
          refine ⟨23947465499544482332875995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63859907998785286221002653 23947465499544482332875995)
          ·
            refine ⟨35921198249316723499313993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23947465499544482332875995 35921198249316723499313993)
            ·
              refine ⟨26940898686987542624485495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35921198249316723499313993 26940898686987542624485495)
              ·
                refine ⟨40411348030481313936728243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26940898686987542624485495 40411348030481313936728243)
                ·
                  refine ⟨60617022045721970905092365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40411348030481313936728243 60617022045721970905092365)
                  ·
                    refine ⟨22731383267145739089409637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60617022045721970905092365 22731383267145739089409637)
                    ·
                      refine ⟨4262134362589826079264307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22731383267145739089409637 4262134362589826079264307)
                      ·
                        rfl

theorem cell23_8300477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_8300477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300477 prefixEnd_8300477 := by exact prefixLift 8300477
  have htrace : WordTrace (prefixWord ++ tailWord_8300477) baseStart_8300477 baseEnd_8300477 := by
    simpa [prefixWord, tailWord_8300477, baseEnd_8300477] using wordTrace_append hprefix tailTrace_8300477
  have hstable : (prefixWord ++ tailWord_8300477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300477).length < 2 ^ (prefixWord ++ tailWord_8300477).sum := by decide
  have hdescent : baseEnd_8300477 < baseStart_8300477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300490 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_8300490 : Nat := 118140960795 + 8300490 * 2 ^ 59
def prefixEnd_8300490 : Nat := 4983230072969 + 3 ^ 40 * 8300490 * 2
def baseEnd_8300490 : Nat := 4262141037838334528401747

theorem tailTrace_8300490 : CollatzResearch.WordTrace tailWord_8300490 prefixEnd_8300490 4262141037838334528401747 := by
  unfold tailWord_8300490
  simp only [CollatzResearch.WordTrace]
  refine ⟨75685935424687453918836731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201829161132499877116897949 75685935424687453918836731)
  ·
    refine ⟨113528903137031180878255097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75685935424687453918836731 113528903137031180878255097)
    ·
      refine ⟨85146677352773385658691323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113528903137031180878255097 85146677352773385658691323)
      ·
        refine ⟨127720016029160078488036985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85146677352773385658691323 127720016029160078488036985)
        ·
          refine ⟨95790012021870058866027739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127720016029160078488036985 95790012021870058866027739)
          ·
            refine ⟨143685018032805088299041609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95790012021870058866027739 143685018032805088299041609)
            ·
              refine ⟨107763763524603816224281207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143685018032805088299041609 107763763524603816224281207)
              ·
                refine ⟨161645645286905724336421811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107763763524603816224281207 161645645286905724336421811)
                ·
                  refine ⟨242468467930358586504632717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161645645286905724336421811 242468467930358586504632717)
                  ·
                    refine ⟨90925675473884469939237269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242468467930358586504632717 90925675473884469939237269)
                    ·
                      refine ⟨4262141037838334528401747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90925675473884469939237269 4262141037838334528401747)
                      ·
                        rfl

theorem cell23_8300490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_8300490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300490 prefixEnd_8300490 := by exact prefixLift 8300490
  have htrace : WordTrace (prefixWord ++ tailWord_8300490) baseStart_8300490 baseEnd_8300490 := by
    simpa [prefixWord, tailWord_8300490, baseEnd_8300490] using wordTrace_append hprefix tailTrace_8300490
  have hstable : (prefixWord ++ tailWord_8300490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300490).length < 2 ^ (prefixWord ++ tailWord_8300490).sum := by decide
  have hdescent : baseEnd_8300490 < baseStart_8300490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300547 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 1, 5]
def baseStart_8300547 : Nat := 118140960795 + 8300547 * 2 ^ 59
def prefixEnd_8300547 : Nat := 4983230072969 + 3 ^ 40 * 8300547 * 2
def baseEnd_8300547 : Nat := 1420723435411880268462995

theorem tailTrace_8300547 : CollatzResearch.WordTrace tailWord_8300547 prefixEnd_8300547 1420723435411880268462995 := by
  unfold tailWord_8300547
  simp only [CollatzResearch.WordTrace]
  refine ⟨302745820659543314410171895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201830547106362209606781263 302745820659543314410171895)
  ·
    refine ⟨454118730989314971615257843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302745820659543314410171895 454118730989314971615257843)
    ·
      refine ⟨681178096483972457422886765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454118730989314971615257843 681178096483972457422886765)
      ·
        refine ⟨255441786181489671533582537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681178096483972457422886765 255441786181489671533582537)
        ·
          refine ⟨191581339636117253650186903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255441786181489671533582537 191581339636117253650186903)
          ·
            refine ⟨287372009454175880475280355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191581339636117253650186903 287372009454175880475280355)
            ·
              refine ⟨431058014181263820712920533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287372009454175880475280355 431058014181263820712920533)
              ·
                refine ⟨10102922207373370797959075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431058014181263820712920533 10102922207373370797959075)
                ·
                  refine ⟨15154383311060056196938613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10102922207373370797959075 15154383311060056196938613)
                  ·
                    refine ⟨1420723435411880268462995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15154383311060056196938613 1420723435411880268462995)
                    ·
                      rfl

theorem cell23_8300547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 5].length) (baseStart_8300547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300547 prefixEnd_8300547 := by exact prefixLift 8300547
  have htrace : WordTrace (prefixWord ++ tailWord_8300547) baseStart_8300547 baseEnd_8300547 := by
    simpa [prefixWord, tailWord_8300547, baseEnd_8300547] using wordTrace_append hprefix tailTrace_8300547
  have hstable : (prefixWord ++ tailWord_8300547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300547).length < 2 ^ (prefixWord ++ tailWord_8300547).sum := by decide
  have hdescent : baseEnd_8300547 < baseStart_8300547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300601 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_8300601 : Nat := 118140960795 + 8300601 * 2 ^ 59
def prefixEnd_8300601 : Nat := 4983230072969 + 3 ^ 40 * 8300601 * 2
def baseEnd_8300601 : Nat := 4262198034190983594113737

theorem tailTrace_8300601 : CollatzResearch.WordTrace tailWord_8300601 prefixEnd_8300601 4262198034190983594113737 := by
  unfold tailWord_8300601
  simp only [CollatzResearch.WordTrace]
  refine ⟨302747790201347681632637657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201831860134231787755091771 302747790201347681632637657)
  ·
    refine ⟨227060842651010761224478243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302747790201347681632637657 227060842651010761224478243)
    ·
      refine ⟨340591263976516141836717365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227060842651010761224478243 340591263976516141836717365)
      ·
        refine ⟨31930430997798388297192253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340591263976516141836717365 31930430997798388297192253)
        ·
          refine ⟨11973911624174395611447095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31930430997798388297192253 11973911624174395611447095)
          ·
            refine ⟨17960867436261593417170643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973911624174395611447095 17960867436261593417170643)
            ·
              refine ⟨26941301154392390125755965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17960867436261593417170643 26941301154392390125755965)
              ·
                refine ⟨10102987932897146297158487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26941301154392390125755965 10102987932897146297158487)
                ·
                  refine ⟨15154481899345719445737731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10102987932897146297158487 15154481899345719445737731)
                  ·
                    refine ⟨22731722849018579168606597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15154481899345719445737731 22731722849018579168606597)
                    ·
                      refine ⟨4262198034190983594113737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22731722849018579168606597 4262198034190983594113737)
                      ·
                        rfl

theorem cell23_8300601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_8300601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300601 prefixEnd_8300601 := by exact prefixLift 8300601
  have htrace : WordTrace (prefixWord ++ tailWord_8300601) baseStart_8300601 baseEnd_8300601 := by
    simpa [prefixWord, tailWord_8300601, baseEnd_8300601] using wordTrace_append hprefix tailTrace_8300601
  have hstable : (prefixWord ++ tailWord_8300601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300601).length < 2 ^ (prefixWord ++ tailWord_8300601).sum := by decide
  have hdescent : baseEnd_8300601 < baseStart_8300601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300647 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_8300647 : Nat := 118140960795 + 8300647 * 2 ^ 59
def prefixEnd_8300647 : Nat := 4983230072969 + 3 ^ 40 * 8300647 * 2
def baseEnd_8300647 : Nat := 4262221654301090414138525

theorem tailTrace_8300647 : CollatzResearch.WordTrace tailWord_8300647 prefixEnd_8300647 4262221654301090414138525 := by
  unfold tailWord_8300647
  simp only [CollatzResearch.WordTrace]
  refine ⟨302749467959181031488812195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201832978639454020992541463 302749467959181031488812195)
  ·
    refine ⟨454124201938771547233218293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302749467959181031488812195 454124201938771547233218293)
    ·
      refine ⟨42574143931759832553114215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454124201938771547233218293 42574143931759832553114215)
      ·
        refine ⟨63861215897639748829671323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42574143931759832553114215 63861215897639748829671323)
        ·
          refine ⟨95791823846459623244506985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63861215897639748829671323 95791823846459623244506985)
          ·
            refine ⟨71843867884844717433380239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95791823846459623244506985 71843867884844717433380239)
            ·
              refine ⟨107765801827267076150070359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71843867884844717433380239 107765801827267076150070359)
              ·
                refine ⟨161648702740900614225105539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107765801827267076150070359 161648702740900614225105539)
                ·
                  refine ⟨242473054111350921337658309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161648702740900614225105539 242473054111350921337658309)
                  ·
                    refine ⟨45463697645878297750810933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242473054111350921337658309 45463697645878297750810933)
                    ·
                      refine ⟨4262221654301090414138525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45463697645878297750810933 4262221654301090414138525)
                      ·
                        rfl

theorem cell23_8300647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_8300647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300647 prefixEnd_8300647 := by exact prefixLift 8300647
  have htrace : WordTrace (prefixWord ++ tailWord_8300647) baseStart_8300647 baseEnd_8300647 := by
    simpa [prefixWord, tailWord_8300647, baseEnd_8300647] using wordTrace_append hprefix tailTrace_8300647
  have hstable : (prefixWord ++ tailWord_8300647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300647).length < 2 ^ (prefixWord ++ tailWord_8300647).sum := by decide
  have hdescent : baseEnd_8300647 < baseStart_8300647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300695 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_8300695 : Nat := 118140960795 + 8300695 * 2 ^ 59
def prefixEnd_8300695 : Nat := 4983230072969 + 3 ^ 40 * 8300695 * 2
def baseEnd_8300695 : Nat := 4262246301372506226338305

theorem tailTrace_8300695 : CollatzResearch.WordTrace tailWord_8300695 prefixEnd_8300695 4262246301372506226338305 := by
  unfold tailWord_8300695
  simp only [CollatzResearch.WordTrace]
  refine ⟨302751218663007135686559539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201834145775338090457706359 302751218663007135686559539)
  ·
    refine ⟨454126827994510703529839309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302751218663007135686559539 454126827994510703529839309)
    ·
      refine ⟨170297560497941513823689741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454126827994510703529839309 170297560497941513823689741)
      ·
        refine ⟨63861585186728067683883653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170297560497941513823689741 63861585186728067683883653)
        ·
          refine ⟨11974047222511512690728185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63861585186728067683883653 11974047222511512690728185)
          ·
            refine ⟨8980535416883634518046139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11974047222511512690728185 8980535416883634518046139)
            ·
              refine ⟨13470803125325451777069209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8980535416883634518046139 13470803125325451777069209)
              ·
                refine ⟨10103102343994088832801907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13470803125325451777069209 10103102343994088832801907)
                ·
                  refine ⟨15154653515991133249202861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103102343994088832801907 15154653515991133249202861)
                  ·
                    refine ⟨5682995068496674968451073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15154653515991133249202861 5682995068496674968451073)
                    ·
                      refine ⟨4262246301372506226338305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5682995068496674968451073 4262246301372506226338305)
                      ·
                        rfl

theorem cell23_8300695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_8300695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300695 prefixEnd_8300695 := by exact prefixLift 8300695
  have htrace : WordTrace (prefixWord ++ tailWord_8300695) baseStart_8300695 baseEnd_8300695 := by
    simpa [prefixWord, tailWord_8300695, baseEnd_8300695] using wordTrace_append hprefix tailTrace_8300695
  have hstable : (prefixWord ++ tailWord_8300695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300695).length < 2 ^ (prefixWord ++ tailWord_8300695).sum := by decide
  have hdescent : baseEnd_8300695 < baseStart_8300695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300697 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 7]
def baseStart_8300697 : Nat := 118140960795 + 8300697 * 2 ^ 59
def prefixEnd_8300697 : Nat := 4983230072969 + 3 ^ 40 * 8300697 * 2
def baseEnd_8300697 : Nat := 473583036481535024279255

theorem tailTrace_8300697 : CollatzResearch.WordTrace tailWord_8300697 prefixEnd_8300697 473583036481535024279255 := by
  unfold tailWord_8300697
  simp only [CollatzResearch.WordTrace]
  refine ⟨302751291608999890028132345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201834194405999926685421563 302751291608999890028132345)
  ·
    refine ⟨227063468706749917521099259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302751291608999890028132345 227063468706749917521099259)
    ·
      refine ⟨340595203060124876281648889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227063468706749917521099259 340595203060124876281648889)
      ·
        refine ⟨255446402295093657211236667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340595203060124876281648889 255446402295093657211236667)
        ·
          refine ⟨383169603442640485816855001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255446402295093657211236667 383169603442640485816855001)
          ·
            refine ⟨287377202581980364362641251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383169603442640485816855001 287377202581980364362641251)
            ·
              refine ⟨431065803872970546543961877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287377202581980364362641251 431065803872970546543961877)
              ·
                refine ⟨20206209556545494369248213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 431065803872970546543961877 20206209556545494369248213)
                ·
                  refine ⟨473583036481535024279255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20206209556545494369248213 473583036481535024279255)
                  ·
                    rfl

theorem cell23_8300697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_8300697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300697 prefixEnd_8300697 := by exact prefixLift 8300697
  have htrace : WordTrace (prefixWord ++ tailWord_8300697) baseStart_8300697 baseEnd_8300697 := by
    simpa [prefixWord, tailWord_8300697, baseEnd_8300697] using wordTrace_append hprefix tailTrace_8300697
  have hstable : (prefixWord ++ tailWord_8300697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300697).length < 2 ^ (prefixWord ++ tailWord_8300697).sum := by decide
  have hdescent : baseEnd_8300697 < baseStart_8300697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300708 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_8300708 : Nat := 118140960795 + 8300708 * 2 ^ 59
def prefixEnd_8300708 : Nat := 4983230072969 + 3 ^ 40 * 8300708 * 2
def baseEnd_8300708 : Nat := 4262252976621014675475745

theorem tailTrace_8300708 : CollatzResearch.WordTrace tailWord_8300708 prefixEnd_8300708 4262252976621014675475745 := by
  unfold tailWord_8300708
  simp only [CollatzResearch.WordTrace]
  refine ⟨151375846405980019453391389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201834461874640025937855185 151375846405980019453391389)
  ·
    refine ⟨56765942402242507295021771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151375846405980019453391389 56765942402242507295021771)
    ·
      refine ⟨85148913603363760942532657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56765942402242507295021771 85148913603363760942532657)
      ·
        refine ⟨63861685202522820706899493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85148913603363760942532657 63861685202522820706899493)
        ·
          refine ⟨11974065975473028882543655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63861685202522820706899493 11974065975473028882543655)
          ·
            refine ⟨17961098963209543323815483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11974065975473028882543655 17961098963209543323815483)
            ·
              refine ⟨26941648444814314985723225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961098963209543323815483 26941648444814314985723225)
              ·
                refine ⟨20206236333610736239292419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26941648444814314985723225 20206236333610736239292419)
                ·
                  refine ⟨30309354500416104358938629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20206236333610736239292419 30309354500416104358938629)
                  ·
                    refine ⟨5683003968828019567300993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30309354500416104358938629 5683003968828019567300993)
                    ·
                      refine ⟨4262252976621014675475745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683003968828019567300993 4262252976621014675475745)
                      ·
                        rfl

theorem cell23_8300708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_8300708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300708 prefixEnd_8300708 := by exact prefixLift 8300708
  have htrace : WordTrace (prefixWord ++ tailWord_8300708) baseStart_8300708 baseEnd_8300708 := by
    simpa [prefixWord, tailWord_8300708, baseEnd_8300708] using wordTrace_append hprefix tailTrace_8300708
  have hstable : (prefixWord ++ tailWord_8300708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300708).length < 2 ^ (prefixWord ++ tailWord_8300708).sum := by decide
  have hdescent : baseEnd_8300708 < baseStart_8300708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300738 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_8300738 : Nat := 118140960795 + 8300738 * 2 ^ 59
def prefixEnd_8300738 : Nat := 4983230072969 + 3 ^ 40 * 8300738 * 2
def baseEnd_8300738 : Nat := 4262268381040649558100607

theorem tailTrace_8300738 : CollatzResearch.WordTrace tailWord_8300738 prefixEnd_8300738 4262268381040649558100607 := by
  unfold tailWord_8300738
  simp only [CollatzResearch.WordTrace]
  refine ⟨75688196750462838507593717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201835191334567569353583245 75688196750462838507593717)
  ·
    refine ⟨7095768445355891110086911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75688196750462838507593717 7095768445355891110086911)
    ·
      refine ⟨10643652668033836665130367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095768445355891110086911 10643652668033836665130367)
      ·
        refine ⟨15965479002050754997695551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643652668033836665130367 15965479002050754997695551)
        ·
          refine ⟨23948218503076132496543327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15965479002050754997695551 23948218503076132496543327)
          ·
            refine ⟨35922327754614198744814991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23948218503076132496543327 35922327754614198744814991)
            ·
              refine ⟨53883491631921298117222487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35922327754614198744814991 53883491631921298117222487)
              ·
                refine ⟨80825237447881947175833731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53883491631921298117222487 80825237447881947175833731)
                ·
                  refine ⟨121237856171822920763750597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80825237447881947175833731 121237856171822920763750597)
                  ·
                    refine ⟨22732098032216797643203237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121237856171822920763750597 22732098032216797643203237)
                    ·
                      refine ⟨4262268381040649558100607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22732098032216797643203237 4262268381040649558100607)
                      ·
                        rfl

theorem cell23_8300738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_8300738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300738 prefixEnd_8300738 := by exact prefixLift 8300738
  have htrace : WordTrace (prefixWord ++ tailWord_8300738) baseStart_8300738 baseEnd_8300738 := by
    simpa [prefixWord, tailWord_8300738, baseEnd_8300738] using wordTrace_append hprefix tailTrace_8300738
  have hstable : (prefixWord ++ tailWord_8300738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300738).length < 2 ^ (prefixWord ++ tailWord_8300738).sum := by decide
  have hdescent : baseEnd_8300738 < baseStart_8300738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300798 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_8300798 : Nat := 118140960795 + 8300798 * 2 ^ 59
def prefixEnd_8300798 : Nat := 4983230072969 + 3 ^ 40 * 8300798 * 2
def baseEnd_8300798 : Nat := 4262299189879919323350331

theorem tailTrace_8300798 : CollatzResearch.WordTrace tailWord_8300798 prefixEnd_8300798 4262299189879919323350331 := by
  unfold tailWord_8300798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37844371922704248034694881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201836650254422656185039365 37844371922704248034694881)
  ·
    refine ⟨28383278942028186026021161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37844371922704248034694881 28383278942028186026021161)
    ·
      refine ⟨21287459206521139519515871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28383278942028186026021161 21287459206521139519515871)
      ·
        refine ⟨31931188809781709279273807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21287459206521139519515871 31931188809781709279273807)
        ·
          refine ⟨47896783214672563918910711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31931188809781709279273807 47896783214672563918910711)
          ·
            refine ⟨71845174822008845878366067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47896783214672563918910711 71845174822008845878366067)
            ·
              refine ⟨107767762233013268817549101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71845174822008845878366067 107767762233013268817549101)
              ·
                refine ⟨40412910837379975806580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107767762233013268817549101 40412910837379975806580913)
                ·
                  refine ⟨30309683128034981854935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40412910837379975806580913 30309683128034981854935685)
                  ·
                    refine ⟨5683065586506559097800441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30309683128034981854935685 5683065586506559097800441)
                    ·
                      refine ⟨4262299189879919323350331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683065586506559097800441 4262299189879919323350331)
                      ·
                        rfl

theorem cell23_8300798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_8300798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300798 prefixEnd_8300798 := by exact prefixLift 8300798
  have htrace : WordTrace (prefixWord ++ tailWord_8300798) baseStart_8300798 baseEnd_8300798 := by
    simpa [prefixWord, tailWord_8300798, baseEnd_8300798] using wordTrace_append hprefix tailTrace_8300798
  have hstable : (prefixWord ++ tailWord_8300798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300798).length < 2 ^ (prefixWord ++ tailWord_8300798).sum := by decide
  have hdescent : baseEnd_8300798 < baseStart_8300798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300842 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_8300842 : Nat := 118140960795 + 8300842 * 2 ^ 59
def prefixEnd_8300842 : Nat := 4983230072969 + 3 ^ 40 * 8300842 * 2
def baseEnd_8300842 : Nat := 1420773927676239050400043

theorem tailTrace_8300842 : CollatzResearch.WordTrace tailWord_8300842 prefixEnd_8300842 1420773927676239050400043 := by
  unfold tailWord_8300842
  simp only [CollatzResearch.WordTrace]
  refine ⟨75689145048368644948040195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201837720128983053194773853 75689145048368644948040195)
  ·
    refine ⟨113533717572552967422060293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75689145048368644948040195 113533717572552967422060293)
    ·
      refine ⟨21287572044853681391636305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113533717572552967422060293 21287572044853681391636305)
      ·
        refine ⟨15965679033640261043727229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21287572044853681391636305 15965679033640261043727229)
        ·
          refine ⟨5987129637615097891397711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15965679033640261043727229 5987129637615097891397711)
          ·
            refine ⟨8980694456422646837096567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987129637615097891397711 8980694456422646837096567)
            ·
              refine ⟨13471041684633970255644851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8980694456422646837096567 13471041684633970255644851)
              ·
                refine ⟨20206562526950955383467277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471041684633970255644851 20206562526950955383467277)
                ·
                  refine ⟨7577460947606608268800229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20206562526950955383467277 7577460947606608268800229)
                  ·
                    refine ⟨1420773927676239050400043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577460947606608268800229 1420773927676239050400043)
                    ·
                      rfl

theorem cell23_8300842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_8300842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300842 prefixEnd_8300842 := by exact prefixLift 8300842
  have htrace : WordTrace (prefixWord ++ tailWord_8300842) baseStart_8300842 baseEnd_8300842 := by
    simpa [prefixWord, tailWord_8300842, baseEnd_8300842] using wordTrace_append hprefix tailTrace_8300842
  have hstable : (prefixWord ++ tailWord_8300842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300842).length < 2 ^ (prefixWord ++ tailWord_8300842).sum := by decide
  have hdescent : baseEnd_8300842 < baseStart_8300842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300871 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_8300871 : Nat := 118140960795 + 8300871 * 2 ^ 59
def prefixEnd_8300871 : Nat := 4983230072969 + 3 ^ 40 * 8300871 * 2
def baseEnd_8300871 : Nat := 4262336673967697537737495

theorem tailTrace_8300871 : CollatzResearch.WordTrace tailWord_8300871 prefixEnd_8300871 4262336673967697537737495 := by
  unfold tailWord_8300871
  simp only [CollatzResearch.WordTrace]
  refine ⟨302757637910369517744966467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201838425273579678496644311 302757637910369517744966467)
  ·
    refine ⟨454136456865554276617449701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302757637910369517744966467 454136456865554276617449701)
    ·
      refine ⟨85150585662291426865771819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454136456865554276617449701 85150585662291426865771819)
      ·
        refine ⟨127725878493437140298657729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85150585662291426865771819 127725878493437140298657729)
        ·
          refine ⟨95794408870077855223993297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127725878493437140298657729 95794408870077855223993297)
          ·
            refine ⟨71845806652558391417994973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95794408870077855223993297 71845806652558391417994973)
            ·
              refine ⟨26942177494709396781748115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71845806652558391417994973 26942177494709396781748115)
              ·
                refine ⟨40413266242064095172622173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26942177494709396781748115 40413266242064095172622173)
                ·
                  refine ⟨15154974840774035689733315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40413266242064095172622173 15154974840774035689733315)
                  ·
                    refine ⟨22732462261161053534599973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15154974840774035689733315 22732462261161053534599973)
                    ·
                      refine ⟨4262336673967697537737495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22732462261161053534599973 4262336673967697537737495)
                      ·
                        rfl

theorem cell23_8300871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_8300871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300871 prefixEnd_8300871 := by exact prefixLift 8300871
  have htrace : WordTrace (prefixWord ++ tailWord_8300871) baseStart_8300871 baseEnd_8300871 := by
    simpa [prefixWord, tailWord_8300871, baseEnd_8300871] using wordTrace_append hprefix tailTrace_8300871
  have hstable : (prefixWord ++ tailWord_8300871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300871).length < 2 ^ (prefixWord ++ tailWord_8300871).sum := by decide
  have hdescent : baseEnd_8300871 < baseStart_8300871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300874 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_8300874 : Nat := 118140960795 + 8300874 * 2 ^ 59
def prefixEnd_8300874 : Nat := 4983230072969 + 3 ^ 40 * 8300874 * 2
def baseEnd_8300874 : Nat := 4262338214409661025999981

theorem tailTrace_8300874 : CollatzResearch.WordTrace tailWord_8300874 prefixEnd_8300874 4262338214409661025999981 := by
  unfold tailWord_8300874
  simp only [CollatzResearch.WordTrace]
  refine ⟨75689436832339662314331419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201838498219572432838217117 75689436832339662314331419)
  ·
    refine ⟨113534155248509493471497129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75689436832339662314331419 113534155248509493471497129)
    ·
      refine ⟨85150616436382120103622847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113534155248509493471497129 85150616436382120103622847)
      ·
        refine ⟨127725924654573180155434271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85150616436382120103622847 127725924654573180155434271)
        ·
          refine ⟨191588886981859770233151407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127725924654573180155434271 191588886981859770233151407)
          ·
            refine ⟨287383330472789655349727111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191588886981859770233151407 287383330472789655349727111)
            ·
              refine ⟨431074995709184483024590667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287383330472789655349727111 431074995709184483024590667)
              ·
                refine ⟨646612493563776724536886001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431074995709184483024590667 646612493563776724536886001)
                ·
                  refine ⟨484959370172832543402664501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646612493563776724536886001 484959370172832543402664501)
                  ·
                    refine ⟨45464940953703050943999797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484959370172832543402664501 45464940953703050943999797)
                    ·
                      refine ⟨4262338214409661025999981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45464940953703050943999797 4262338214409661025999981)
                      ·
                        rfl

theorem cell23_8300874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_8300874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300874 prefixEnd_8300874 := by exact prefixLift 8300874
  have htrace : WordTrace (prefixWord ++ tailWord_8300874) baseStart_8300874 baseEnd_8300874 := by
    simpa [prefixWord, tailWord_8300874, baseEnd_8300874] using wordTrace_append hprefix tailTrace_8300874
  have hstable : (prefixWord ++ tailWord_8300874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300874).length < 2 ^ (prefixWord ++ tailWord_8300874).sum := by decide
  have hdescent : baseEnd_8300874 < baseStart_8300874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300881 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_8300881 : Nat := 118140960795 + 8300881 * 2 ^ 59
def prefixEnd_8300881 : Nat := 4983230072969 + 3 ^ 40 * 8300881 * 2
def baseEnd_8300881 : Nat := 1420780602924747499537483

theorem tailTrace_8300881 : CollatzResearch.WordTrace tailWord_8300881 prefixEnd_8300881 1420780602924747499537483 := by
  unfold tailWord_8300881
  simp only [CollatzResearch.WordTrace]
  refine ⟨302758002640333289452830497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201838668426888859635220331 302758002640333289452830497)
  ·
    refine ⟨227068501980249967089622873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302758002640333289452830497 227068501980249967089622873)
    ·
      refine ⟨170301376485187475317217155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227068501980249967089622873 170301376485187475317217155)
      ·
        refine ⟨255452064727781212975825733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170301376485187475317217155 255452064727781212975825733)
        ·
          refine ⟨47897262136458977432967325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255452064727781212975825733 47897262136458977432967325)
          ·
            refine ⟨17961473301172116537362747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47897262136458977432967325 17961473301172116537362747)
            ·
              refine ⟨26942209951758174806044121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961473301172116537362747 26942209951758174806044121)
              ·
                refine ⟨20206657463818631104533091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26942209951758174806044121 20206657463818631104533091)
                ·
                  refine ⟨30309986195727946656799637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20206657463818631104533091 30309986195727946656799637)
                  ·
                    refine ⟨1420780602924747499537483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30309986195727946656799637 1420780602924747499537483)
                    ·
                      rfl

theorem cell23_8300881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_8300881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300881 prefixEnd_8300881 := by exact prefixLift 8300881
  have htrace : WordTrace (prefixWord ++ tailWord_8300881) baseStart_8300881 baseEnd_8300881 := by
    simpa [prefixWord, tailWord_8300881, baseEnd_8300881] using wordTrace_append hprefix tailTrace_8300881
  have hstable : (prefixWord ++ tailWord_8300881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300881).length < 2 ^ (prefixWord ++ tailWord_8300881).sum := by decide
  have hdescent : baseEnd_8300881 < baseStart_8300881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300885 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_8300885 : Nat := 118140960795 + 8300885 * 2 ^ 59
def prefixEnd_8300885 : Nat := 4983230072969 + 3 ^ 40 * 8300885 * 2
def baseEnd_8300885 : Nat := 1420781287565620160987477

theorem tailTrace_8300885 : CollatzResearch.WordTrace tailWord_8300885 prefixEnd_8300885 1420781287565620160987477 := by
  unfold tailWord_8300885
  simp only [CollatzResearch.WordTrace]
  refine ⟨302758148532318798135976109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201838765688212532090650739 302758148532318798135976109)
  ·
    refine ⟨113534305699619549300991041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302758148532318798135976109 113534305699619549300991041)
    ·
      refine ⟨85150729274714661975743281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113534305699619549300991041 85150729274714661975743281)
      ·
        refine ⟨63863046956035996481807461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85150729274714661975743281 63863046956035996481807461)
        ·
          refine ⟨11974321304256749340338899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63863046956035996481807461 11974321304256749340338899)
          ·
            refine ⟨17961481956385124010508349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11974321304256749340338899 17961481956385124010508349)
            ·
              refine ⟨6735555733644421503940631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17961481956385124010508349 6735555733644421503940631)
              ·
                refine ⟨10103333600466632255910947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735555733644421503940631 10103333600466632255910947)
                ·
                  refine ⟨15155000400699948383866421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103333600466632255910947 15155000400699948383866421)
                  ·
                    refine ⟨1420781287565620160987477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155000400699948383866421 1420781287565620160987477)
                    ·
                      rfl

theorem cell23_8300885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_8300885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300885 prefixEnd_8300885 := by exact prefixLift 8300885
  have htrace : WordTrace (prefixWord ++ tailWord_8300885) baseStart_8300885 baseEnd_8300885 := by
    simpa [prefixWord, tailWord_8300885, baseEnd_8300885] using wordTrace_append hprefix tailTrace_8300885
  have hstable : (prefixWord ++ tailWord_8300885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300885).length < 2 ^ (prefixWord ++ tailWord_8300885).sum := by decide
  have hdescent : baseEnd_8300885 < baseStart_8300885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300888 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_8300888 : Nat := 118140960795 + 8300888 * 2 ^ 59
def prefixEnd_8300888 : Nat := 4983230072969 + 3 ^ 40 * 8300888 * 2
def baseEnd_8300888 : Nat := 4262345403138823971224917

theorem tailTrace_8300888 : CollatzResearch.WordTrace tailWord_8300888 prefixEnd_8300888 4262345403138823971224917 := by
  unfold tailWord_8300888
  simp only [CollatzResearch.WordTrace]
  refine ⟨151379128975653964824167659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201838838634205286432223545 151379128975653964824167659)
  ·
    refine ⟨227068693463480947236251489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151379128975653964824167659 227068693463480947236251489)
    ·
      refine ⟨170301520097610710427188617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227068693463480947236251489 170301520097610710427188617)
      ·
        refine ⟨127726140073208032820391463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170301520097610710427188617 127726140073208032820391463)
        ·
          refine ⟨191589210109812049230587195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127726140073208032820391463 191589210109812049230587195)
          ·
            refine ⟨287383815164718073845880793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191589210109812049230587195 287383815164718073845880793)
            ·
              refine ⟨215537861373538555384410595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287383815164718073845880793 215537861373538555384410595)
              ·
                refine ⟨323306792060307833076615893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215537861373538555384410595 323306792060307833076615893)
                ·
                  refine ⟨7577502938913464837733185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 323306792060307833076615893 7577502938913464837733185)
                  ·
                    refine ⟨5683127204185098628299889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7577502938913464837733185 5683127204185098628299889)
                    ·
                      refine ⟨4262345403138823971224917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683127204185098628299889 4262345403138823971224917)
                      ·
                        rfl

theorem cell23_8300888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_8300888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300888 prefixEnd_8300888 := by exact prefixLift 8300888
  have htrace : WordTrace (prefixWord ++ tailWord_8300888) baseStart_8300888 baseEnd_8300888 := by
    simpa [prefixWord, tailWord_8300888, baseEnd_8300888] using wordTrace_append hprefix tailTrace_8300888
  have hstable : (prefixWord ++ tailWord_8300888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300888).length < 2 ^ (prefixWord ++ tailWord_8300888).sum := by decide
  have hdescent : baseEnd_8300888 < baseStart_8300888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300942 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_8300942 : Nat := 118140960795 + 8300942 * 2 ^ 59
def prefixEnd_8300942 : Nat := 4983230072969 + 3 ^ 40 * 8300942 * 2
def baseEnd_8300942 : Nat := 4262373131094166759949669

theorem tailTrace_8300942 : CollatzResearch.WordTrace tailWord_8300942 prefixEnd_8300942 4262373131094166759949669 := by
  unfold tailWord_8300942
  simp only [CollatzResearch.WordTrace]
  refine ⟨37845028436639037108850135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201840151662074864580534053 37845028436639037108850135)
  ·
    refine ⟨56767542654958555663275203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37845028436639037108850135 56767542654958555663275203)
    ·
      refine ⟨85151313982437833494912805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56767542654958555663275203 85151313982437833494912805)
      ·
        refine ⟨15965871371707093780296151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85151313982437833494912805 15965871371707093780296151)
        ·
          refine ⟨23948807057560640670444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15965871371707093780296151 23948807057560640670444227)
          ·
            refine ⟨35923210586340961005666341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23948807057560640670444227 35923210586340961005666341)
            ·
              refine ⟨6735601984938930188562439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35923210586340961005666341 6735601984938930188562439)
              ·
                refine ⟨10103402977408395282843659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735601984938930188562439 10103402977408395282843659)
                ·
                  refine ⟨15155104466112592924265489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103402977408395282843659 15155104466112592924265489)
                  ·
                    refine ⟨11366328349584444693199117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15155104466112592924265489 11366328349584444693199117)
                    ·
                      refine ⟨4262373131094166759949669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11366328349584444693199117 4262373131094166759949669)
                      ·
                        rfl

theorem cell23_8300942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_8300942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300942 prefixEnd_8300942 := by exact prefixLift 8300942
  have htrace : WordTrace (prefixWord ++ tailWord_8300942) baseStart_8300942 baseEnd_8300942 := by
    simpa [prefixWord, tailWord_8300942, baseEnd_8300942] using wordTrace_append hprefix tailTrace_8300942
  have hstable : (prefixWord ++ tailWord_8300942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300942).length < 2 ^ (prefixWord ++ tailWord_8300942).sum := by decide
  have hdescent : baseEnd_8300942 < baseStart_8300942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8300944 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_8300944 : Nat := 118140960795 + 8300944 * 2 ^ 59
def prefixEnd_8300944 : Nat := 4983230072969 + 3 ^ 40 * 8300944 * 2
def baseEnd_8300944 : Nat := 4262374158055475752124659

theorem tailTrace_8300944 : CollatzResearch.WordTrace tailWord_8300944 prefixEnd_8300944 4262374158055475752124659 := by
  unfold tailWord_8300944
  simp only [CollatzResearch.WordTrace]
  refine ⟨151380150219552525606186943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201840200292736700808249257 151380150219552525606186943)
  ·
    refine ⟨227070225329328788409280415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151380150219552525606186943 227070225329328788409280415)
    ·
      refine ⟨340605337993993182613920623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227070225329328788409280415 340605337993993182613920623)
      ·
        refine ⟨510908006990989773920880935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340605337993993182613920623 510908006990989773920880935)
        ·
          refine ⟨766362010486484660881321403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510908006990989773920880935 766362010486484660881321403)
          ·
            refine ⟨1149543015729726991321982105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766362010486484660881321403 1149543015729726991321982105)
            ·
              refine ⟨862157261797295243491486579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149543015729726991321982105 862157261797295243491486579)
              ·
                refine ⟨1293235892695942865237229869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862157261797295243491486579 1293235892695942865237229869)
                ·
                  refine ⟨484963459760978574463961201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1293235892695942865237229869 484963459760978574463961201)
                  ·
                    refine ⟨363722594820733930847970901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484963459760978574463961201 363722594820733930847970901)
                    ·
                      refine ⟨4262374158055475752124659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 363722594820733930847970901 4262374158055475752124659)
                      ·
                        rfl

theorem cell23_8300944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_8300944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8300944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8300944 prefixEnd_8300944 := by exact prefixLift 8300944
  have htrace : WordTrace (prefixWord ++ tailWord_8300944) baseStart_8300944 baseEnd_8300944 := by
    simpa [prefixWord, tailWord_8300944, baseEnd_8300944] using wordTrace_append hprefix tailTrace_8300944
  have hstable : (prefixWord ++ tailWord_8300944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8300944).length < 2 ^ (prefixWord ++ tailWord_8300944).sum := by decide
  have hdescent : baseEnd_8300944 < baseStart_8300944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8300944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301012 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_8301012 : Nat := 118140960795 + 8301012 * 2 ^ 59
def prefixEnd_8301012 : Nat := 4983230072969 + 3 ^ 40 * 8301012 * 2
def baseEnd_8301012 : Nat := 4262409074739981486074347

theorem tailTrace_8301012 : CollatzResearch.WordTrace tailWord_8301012 prefixEnd_8301012 4262409074739981486074347 := by
  unfold tailWord_8301012
  simp only [CollatzResearch.WordTrace]
  refine ⟨151381390301429349412924645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201841853735239132550566193 151381390301429349412924645)
  ·
    refine ⟨28384010681518003014923371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151381390301429349412924645 28384010681518003014923371)
    ·
      refine ⟨42576016022277004522385057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28384010681518003014923371 42576016022277004522385057)
      ·
        refine ⟨31932012016707753391788793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42576016022277004522385057 31932012016707753391788793)
        ·
          refine ⟨23949009012530815043841595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31932012016707753391788793 23949009012530815043841595)
          ·
            refine ⟨35923513518796222565762393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23949009012530815043841595 35923513518796222565762393)
            ·
              refine ⟨26942635139097166924321795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35923513518796222565762393 26942635139097166924321795)
              ·
                refine ⟨40413952708645750386482693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26942635139097166924321795 40413952708645750386482693)
                ·
                  refine ⟨7577616132871078197465505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40413952708645750386482693 7577616132871078197465505)
                  ·
                    refine ⟨5683212099653308648099129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7577616132871078197465505 5683212099653308648099129)
                    ·
                      refine ⟨4262409074739981486074347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683212099653308648099129 4262409074739981486074347)
                      ·
                        rfl

theorem cell23_8301012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_8301012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301012 prefixEnd_8301012 := by exact prefixLift 8301012
  have htrace : WordTrace (prefixWord ++ tailWord_8301012) baseStart_8301012 baseEnd_8301012 := by
    simpa [prefixWord, tailWord_8301012, baseEnd_8301012] using wordTrace_append hprefix tailTrace_8301012
  have hstable : (prefixWord ++ tailWord_8301012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301012).length < 2 ^ (prefixWord ++ tailWord_8301012).sum := by decide
  have hdescent : baseEnd_8301012 < baseStart_8301012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301029 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_8301029 : Nat := 118140960795 + 8301029 * 2 ^ 59
def prefixEnd_8301029 : Nat := 4983230072969 + 3 ^ 40 * 8301029 * 2
def baseEnd_8301029 : Nat := 4262417803911107919561769

theorem tailTrace_8301029 : CollatzResearch.WordTrace tailWord_8301029 prefixEnd_8301029 4262417803911107919561769 := by
  unfold tailWord_8301029
  simp only [CollatzResearch.WordTrace]
  refine ⟨302763400643797110729218141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201842267095864740486145427 302763400643797110729218141)
  ·
    refine ⟨113536275241423916523456803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302763400643797110729218141 113536275241423916523456803)
    ·
      refine ⟨170304412862135874785185205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113536275241423916523456803 170304412862135874785185205)
      ·
        refine ⟨15966038705825238261111113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170304412862135874785185205 15966038705825238261111113)
        ·
          refine ⟨11974529029368928695833335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15966038705825238261111113 11974529029368928695833335)
          ·
            refine ⟨17961793544053393043750003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11974529029368928695833335 17961793544053393043750003)
            ·
              refine ⟨26942690316080089565625005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961793544053393043750003 26942690316080089565625005)
              ·
                refine ⟨10103508868530033587109377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26942690316080089565625005 10103508868530033587109377)
                ·
                  refine ⟨7577631651397525190332033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10103508868530033587109377 7577631651397525190332033)
                  ·
                    refine ⟨5683223738548143892749025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7577631651397525190332033 5683223738548143892749025)
                    ·
                      refine ⟨4262417803911107919561769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683223738548143892749025 4262417803911107919561769)
                      ·
                        rfl

theorem cell23_8301029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_8301029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301029 prefixEnd_8301029 := by exact prefixLift 8301029
  have htrace : WordTrace (prefixWord ++ tailWord_8301029) baseStart_8301029 baseEnd_8301029 := by
    simpa [prefixWord, tailWord_8301029, baseEnd_8301029] using wordTrace_append hprefix tailTrace_8301029
  have hstable : (prefixWord ++ tailWord_8301029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301029).length < 2 ^ (prefixWord ++ tailWord_8301029).sum := by decide
  have hdescent : baseEnd_8301029 < baseStart_8301029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301041 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_8301041 : Nat := 118140960795 + 8301041 * 2 ^ 59
def prefixEnd_8301041 : Nat := 4983230072969 + 3 ^ 40 * 8301041 * 2
def baseEnd_8301041 : Nat := 4262423965678961872611713

theorem tailTrace_8301041 : CollatzResearch.WordTrace tailWord_8301041 prefixEnd_8301041 4262423965678961872611713 := by
  unfold tailWord_8301041
  simp only [CollatzResearch.WordTrace]
  refine ⟨302763838319753636778654977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201842558879835757852436651 302763838319753636778654977)
  ·
    refine ⟨227072878739815227583991233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302763838319753636778654977 227072878739815227583991233)
    ·
      refine ⟨170304659054861420687993425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227072878739815227583991233 170304659054861420687993425)
      ·
        refine ⟨127728494291146065515995069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170304659054861420687993425 127728494291146065515995069)
        ·
          refine ⟨47898185359179774568498151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127728494291146065515995069 47898185359179774568498151)
          ·
            refine ⟨71847278038769661852747227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47898185359179774568498151 71847278038769661852747227)
            ·
              refine ⟨107770917058154492779120841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71847278038769661852747227 107770917058154492779120841)
              ·
                refine ⟨80828187793615869584340631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107770917058154492779120841 80828187793615869584340631)
                ·
                  refine ⟨121242281690423804376510947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80828187793615869584340631 121242281690423804376510947)
                  ·
                    refine ⟨181863422535635706564766421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121242281690423804376510947 181863422535635706564766421)
                    ·
                      refine ⟨4262423965678961872611713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181863422535635706564766421 4262423965678961872611713)
                      ·
                        rfl

theorem cell23_8301041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_8301041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301041 prefixEnd_8301041 := by exact prefixLift 8301041
  have htrace : WordTrace (prefixWord ++ tailWord_8301041) baseStart_8301041 baseEnd_8301041 := by
    simpa [prefixWord, tailWord_8301041, baseEnd_8301041] using wordTrace_append hprefix tailTrace_8301041
  have hstable : (prefixWord ++ tailWord_8301041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301041).length < 2 ^ (prefixWord ++ tailWord_8301041).sum := by decide
  have hdescent : baseEnd_8301041 < baseStart_8301041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301048 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_8301048 : Nat := 118140960795 + 8301048 * 2 ^ 59
def prefixEnd_8301048 : Nat := 4983230072969 + 3 ^ 40 * 8301048 * 2
def baseEnd_8301048 : Nat := 1420809186681181115074727

theorem tailTrace_8301048 : CollatzResearch.WordTrace tailWord_8301048 prefixEnd_8301048 1420809186681181115074727 := by
  unfold tailWord_8301048
  simp only [CollatzResearch.WordTrace]
  refine ⟨151382046815364138487079899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201842729087152184649439865 151382046815364138487079899)
  ·
    refine ⟨227073070223046207730619849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151382046815364138487079899 227073070223046207730619849)
    ·
      refine ⟨170304802667284655797964887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227073070223046207730619849 170304802667284655797964887)
      ·
        refine ⟨255457204000926983696947331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170304802667284655797964887 255457204000926983696947331)
        ·
          refine ⟨383185806001390475545420997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255457204000926983696947331 383185806001390475545420997)
          ·
            refine ⟨71847338625260714164766437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383185806001390475545420997 71847338625260714164766437)
            ·
              refine ⟨13471375992236383905893707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71847338625260714164766437 13471375992236383905893707)
              ·
                refine ⟨20207063988354575858840561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471375992236383905893707 20207063988354575858840561)
                ·
                  refine ⟨15155297991265931894130421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20207063988354575858840561 15155297991265931894130421)
                  ·
                    refine ⟨1420809186681181115074727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155297991265931894130421 1420809186681181115074727)
                    ·
                      rfl

theorem cell23_8301048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_8301048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301048 prefixEnd_8301048 := by exact prefixLift 8301048
  have htrace : WordTrace (prefixWord ++ tailWord_8301048) baseStart_8301048 baseEnd_8301048 := by
    simpa [prefixWord, tailWord_8301048, baseEnd_8301048] using wordTrace_append hprefix tailTrace_8301048
  have hstable : (prefixWord ++ tailWord_8301048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301048).length < 2 ^ (prefixWord ++ tailWord_8301048).sum := by decide
  have hdescent : baseEnd_8301048 < baseStart_8301048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301069 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 5]
def baseStart_8301069 : Nat := 118140960795 + 8301069 * 2 ^ 59
def prefixEnd_8301069 : Nat := 4983230072969 + 3 ^ 40 * 8301069 * 2
def baseEnd_8301069 : Nat := 473604260348587529229065

theorem tailTrace_8301069 : CollatzResearch.WordTrace tailWord_8301069 prefixEnd_8301069 473604260348587529229065 := by
  unfold tailWord_8301069
  simp only [CollatzResearch.WordTrace]
  refine ⟨302764859563652197560674261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201843239709101465040449507 302764859563652197560674261)
  ·
    refine ⟨7096051396023098380328303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 302764859563652197560674261 7096051396023098380328303)
    ·
      refine ⟨10644077094034647570492455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096051396023098380328303 10644077094034647570492455)
      ·
        refine ⟨15966115641051971355738683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644077094034647570492455 15966115641051971355738683)
        ·
          refine ⟨23949173461577957033608025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15966115641051971355738683 23949173461577957033608025)
          ·
            refine ⟨17961880096183467775206019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23949173461577957033608025 17961880096183467775206019)
            ·
              refine ⟨26942820144275201662809029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961880096183467775206019 26942820144275201662809029)
              ·
                refine ⟨5051778777051600311776693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26942820144275201662809029 5051778777051600311776693)
                ·
                  refine ⟨473604260348587529229065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5051778777051600311776693 473604260348587529229065)
                  ·
                    rfl

theorem cell23_8301069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_8301069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301069 prefixEnd_8301069 := by exact prefixLift 8301069
  have htrace : WordTrace (prefixWord ++ tailWord_8301069) baseStart_8301069 baseEnd_8301069 := by
    simpa [prefixWord, tailWord_8301069, baseEnd_8301069] using wordTrace_append hprefix tailTrace_8301069
  have hstable : (prefixWord ++ tailWord_8301069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301069).length < 2 ^ (prefixWord ++ tailWord_8301069).sum := by decide
  have hdescent : baseEnd_8301069 < baseStart_8301069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301081 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_8301081 : Nat := 118140960795 + 8301081 * 2 ^ 59
def prefixEnd_8301081 : Nat := 4983230072969 + 3 ^ 40 * 8301081 * 2
def baseEnd_8301081 : Nat := 4262444504905141716111529

theorem tailTrace_8301081 : CollatzResearch.WordTrace tailWord_8301081 prefixEnd_8301081 4262444504905141716111529 := by
  unfold tailWord_8301081
  simp only [CollatzResearch.WordTrace]
  refine ⟨302765297239608723610111097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201843531493072482406740731 302765297239608723610111097)
  ·
    refine ⟨227073972929706542707583323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302765297239608723610111097 227073972929706542707583323)
    ·
      refine ⟨340610959394559814061374985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227073972929706542707583323 340610959394559814061374985)
      ·
        refine ⟨255458219545919860546031239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340610959394559814061374985 255458219545919860546031239)
        ·
          refine ⟨383187329318879790819046859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255458219545919860546031239 383187329318879790819046859)
          ·
            refine ⟨574780993978319686228570289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383187329318879790819046859 574780993978319686228570289)
            ·
              refine ⟨431085745483739764671427717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574780993978319686228570289 431085745483739764671427717)
              ·
                refine ⟨80828577278201205875892697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431085745483739764671427717 80828577278201205875892697)
                ·
                  refine ⟨60621432958650904406919523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80828577278201205875892697 60621432958650904406919523)
                  ·
                    refine ⟨90932149437976356610379285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60621432958650904406919523 90932149437976356610379285)
                    ·
                      refine ⟨4262444504905141716111529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90932149437976356610379285 4262444504905141716111529)
                      ·
                        rfl

theorem cell23_8301081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_8301081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301081 prefixEnd_8301081 := by exact prefixLift 8301081
  have htrace : WordTrace (prefixWord ++ tailWord_8301081) baseStart_8301081 baseEnd_8301081 := by
    simpa [prefixWord, tailWord_8301081, baseEnd_8301081] using wordTrace_append hprefix tailTrace_8301081
  have hstable : (prefixWord ++ tailWord_8301081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301081).length < 2 ^ (prefixWord ++ tailWord_8301081).sum := by decide
  have hdescent : baseEnd_8301081 < baseStart_8301081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301085 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_8301085 : Nat := 118140960795 + 8301085 * 2 ^ 59
def prefixEnd_8301085 : Nat := 4983230072969 + 3 ^ 40 * 8301085 * 2
def baseEnd_8301085 : Nat := 4262446558827759700461511

theorem tailTrace_8301085 : CollatzResearch.WordTrace tailWord_8301085 prefixEnd_8301085 4262446558827759700461511 := by
  unfold tailWord_8301085
  simp only [CollatzResearch.WordTrace]
  refine ⟨302765443131594232293256709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201843628754396154862171139 302765443131594232293256709)
  ·
    refine ⟨56768520587173918554985633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302765443131594232293256709 56768520587173918554985633)
    ·
      refine ⟨42576390440380438916239225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56768520587173918554985633 42576390440380438916239225)
      ·
        refine ⟨31932292830285329187179419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42576390440380438916239225 31932292830285329187179419)
        ·
          refine ⟨47898439245427993780769129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31932292830285329187179419 47898439245427993780769129)
          ·
            refine ⟨35923829434070995335576847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47898439245427993780769129 35923829434070995335576847)
            ·
              refine ⟨53885744151106493003365271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35923829434070995335576847 53885744151106493003365271)
              ·
                refine ⟨80828616226659739505047907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53885744151106493003365271 80828616226659739505047907)
                ·
                  refine ⟨121242924339989609257571861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80828616226659739505047907 121242924339989609257571861)
                  ·
                    refine ⟨5683262078437012933948681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121242924339989609257571861 5683262078437012933948681)
                    ·
                      refine ⟨4262446558827759700461511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683262078437012933948681 4262446558827759700461511)
                      ·
                        rfl

theorem cell23_8301085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_8301085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301085 prefixEnd_8301085 := by exact prefixLift 8301085
  have htrace : WordTrace (prefixWord ++ tailWord_8301085) baseStart_8301085 baseEnd_8301085 := by
    simpa [prefixWord, tailWord_8301085, baseEnd_8301085] using wordTrace_append hprefix tailTrace_8301085
  have hstable : (prefixWord ++ tailWord_8301085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301085).length < 2 ^ (prefixWord ++ tailWord_8301085).sum := by decide
  have hdescent : baseEnd_8301085 < baseStart_8301085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301105 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_8301105 : Nat := 118140960795 + 8301105 * 2 ^ 59
def prefixEnd_8301105 : Nat := 4983230072969 + 3 ^ 40 * 8301105 * 2
def baseEnd_8301105 : Nat := 4262456828440849622211419

theorem tailTrace_8301105 : CollatzResearch.WordTrace tailWord_8301105 prefixEnd_8301105 4262456828440849622211419 := by
  unfold tailWord_8301105
  simp only [CollatzResearch.WordTrace]
  refine ⟨302766172591521775708984769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201844115061014517139323179 302766172591521775708984769)
  ·
    refine ⟨227074629443641331781738577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302766172591521775708984769 227074629443641331781738577)
    ·
      refine ⟨170305972082730998836303933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227074629443641331781738577 170305972082730998836303933)
      ·
        refine ⟨63864739531024124563613975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170305972082730998836303933 63864739531024124563613975)
        ·
          refine ⟨95797109296536186845420963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63864739531024124563613975 95797109296536186845420963)
          ·
            refine ⟨143695663944804280268131445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95797109296536186845420963 143695663944804280268131445)
            ·
              refine ⟨13471468494825401275137323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143695663944804280268131445 13471468494825401275137323)
              ·
                refine ⟨20207202742238101912705985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471468494825401275137323 20207202742238101912705985)
                ·
                  refine ⟨15155402056678576434529489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20207202742238101912705985 15155402056678576434529489)
                  ·
                    refine ⟨11366551542508932325897117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15155402056678576434529489 11366551542508932325897117)
                    ·
                      refine ⟨4262456828440849622211419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11366551542508932325897117 4262456828440849622211419)
                      ·
                        rfl

theorem cell23_8301105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_8301105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301105 prefixEnd_8301105 := by exact prefixLift 8301105
  have htrace : WordTrace (prefixWord ++ tailWord_8301105) baseStart_8301105 baseEnd_8301105 := by
    simpa [prefixWord, tailWord_8301105, baseEnd_8301105] using wordTrace_append hprefix tailTrace_8301105
  have hstable : (prefixWord ++ tailWord_8301105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301105).length < 2 ^ (prefixWord ++ tailWord_8301105).sum := by decide
  have hdescent : baseEnd_8301105 < baseStart_8301105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301112 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 1, 4]
def baseStart_8301112 : Nat := 118140960795 + 8301112 * 2 ^ 59
def prefixEnd_8301112 : Nat := 4983230072969 + 3 ^ 40 * 8301112 * 2
def baseEnd_8301112 : Nat := 1420820140935143698274629

theorem tailTrace_8301112 : CollatzResearch.WordTrace tailWord_8301112 prefixEnd_8301112 1420820140935143698274629 := by
  unfold tailWord_8301112
  simp only [CollatzResearch.WordTrace]
  refine ⟨151383213951248207952244795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201844285268330943936326393 151383213951248207952244795)
  ·
    refine ⟨227074820926872311928367193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151383213951248207952244795 227074820926872311928367193)
    ·
      refine ⟨170306115695154233946275395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227074820926872311928367193 170306115695154233946275395)
      ·
        refine ⟨255459173542731350919413093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170306115695154233946275395 255459173542731350919413093)
        ·
          refine ⟨47898595039262128297389955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255459173542731350919413093 47898595039262128297389955)
          ·
            refine ⟨71847892558893192446084933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47898595039262128297389955 71847892558893192446084933)
            ·
              refine ⟨13471479854792473583640925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71847892558893192446084933 13471479854792473583640925)
              ·
                refine ⟨5051804945547177593865347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13471479854792473583640925 5051804945547177593865347)
                ·
                  refine ⟨7577707418320766390798021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051804945547177593865347 7577707418320766390798021)
                  ·
                    refine ⟨1420820140935143698274629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577707418320766390798021 1420820140935143698274629)
                    ·
                      rfl

theorem cell23_8301112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_8301112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301112 prefixEnd_8301112 := by exact prefixLift 8301112
  have htrace : WordTrace (prefixWord ++ tailWord_8301112) baseStart_8301112 baseEnd_8301112 := by
    simpa [prefixWord, tailWord_8301112, baseEnd_8301112] using wordTrace_append hprefix tailTrace_8301112
  have hstable : (prefixWord ++ tailWord_8301112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301112).length < 2 ^ (prefixWord ++ tailWord_8301112).sum := by decide
  have hdescent : baseEnd_8301112 < baseStart_8301112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301125 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 6]
def baseStart_8301125 : Nat := 118140960795 + 8301125 * 2 ^ 59
def prefixEnd_8301125 : Nat := 4983230072969 + 3 ^ 40 * 8301125 * 2
def baseEnd_8301125 : Nat := 473607455339326615995703

theorem tailTrace_8301125 : CollatzResearch.WordTrace tailWord_8301125 prefixEnd_8301125 473607455339326615995703 := by
  unfold tailWord_8301125
  simp only [CollatzResearch.WordTrace]
  refine ⟨302766902051449319124712829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201844601367632879416475219 302766902051449319124712829)
  ·
    refine ⟨113537588269293494671767311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302766902051449319124712829 113537588269293494671767311)
    ·
      refine ⟨170306382403940242007650967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113537588269293494671767311 170306382403940242007650967)
      ·
        refine ⟨255459573605910363011476451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170306382403940242007650967 255459573605910363011476451)
        ·
          refine ⟨383189360408865544517214677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255459573605910363011476451 383189360408865544517214677)
          ·
            refine ⟨8981000634582786199622219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 383189360408865544517214677 8981000634582786199622219)
            ·
              refine ⟨13471500951874179299433329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981000634582786199622219 13471500951874179299433329)
              ·
                refine ⟨10103625713905634474574997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13471500951874179299433329 10103625713905634474574997)
                ·
                  refine ⟨473607455339326615995703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10103625713905634474574997 473607455339326615995703)
                  ·
                    rfl

theorem cell23_8301125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_8301125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301125 prefixEnd_8301125 := by exact prefixLift 8301125
  have htrace : WordTrace (prefixWord ++ tailWord_8301125) baseStart_8301125 baseEnd_8301125 := by
    simpa [prefixWord, tailWord_8301125, baseEnd_8301125] using wordTrace_append hprefix tailTrace_8301125
  have hstable : (prefixWord ++ tailWord_8301125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301125).length < 2 ^ (prefixWord ++ tailWord_8301125).sum := by decide
  have hdescent : baseEnd_8301125 < baseStart_8301125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301135 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 3]
def baseStart_8301135 : Nat := 118140960795 + 8301135 * 2 ^ 59
def prefixEnd_8301135 : Nat := 4983230072969 + 3 ^ 40 * 8301135 * 2
def baseEnd_8301135 : Nat := 4262472232860484504836281

theorem tailTrace_8301135 : CollatzResearch.WordTrace tailWord_8301135 prefixEnd_8301135 4262472232860484504836281 := by
  unfold tailWord_8301135
  simp only [CollatzResearch.WordTrace]
  refine ⟨302767266781413090832576859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201844844520942060555051239 302767266781413090832576859)
  ·
    refine ⟨454150900172119636248865289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302767266781413090832576859 454150900172119636248865289)
    ·
      refine ⟨340613175129089727186648967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454150900172119636248865289 340613175129089727186648967)
      ·
        refine ⟨510919762693634590779973451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340613175129089727186648967 510919762693634590779973451)
        ·
          refine ⟨766379644040451886169960177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510919762693634590779973451 766379644040451886169960177)
          ·
            refine ⟨574784733030338914627470133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766379644040451886169960177 574784733030338914627470133)
            ·
              refine ⟨53886068721594273246325325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 574784733030338914627470133 53886068721594273246325325)
              ·
                refine ⟨20207275770597852467371997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53886068721594273246325325 20207275770597852467371997)
                ·
                  refine ⟨7577728413974194675264499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20207275770597852467371997 7577728413974194675264499)
                  ·
                    refine ⟨11366592620961292012896749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7577728413974194675264499 11366592620961292012896749)
                    ·
                      refine ⟨4262472232860484504836281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11366592620961292012896749 4262472232860484504836281)
                      ·
                        rfl

theorem cell23_8301135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_8301135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301135 prefixEnd_8301135 := by exact prefixLift 8301135
  have htrace : WordTrace (prefixWord ++ tailWord_8301135) baseStart_8301135 baseEnd_8301135 := by
    simpa [prefixWord, tailWord_8301135, baseEnd_8301135] using wordTrace_append hprefix tailTrace_8301135
  have hstable : (prefixWord ++ tailWord_8301135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301135).length < 2 ^ (prefixWord ++ tailWord_8301135).sum := by decide
  have hdescent : baseEnd_8301135 < baseStart_8301135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301155 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 1, 5]
def baseStart_8301155 : Nat := 118140960795 + 8301155 * 2 ^ 59
def prefixEnd_8301155 : Nat := 4983230072969 + 3 ^ 40 * 8301155 * 2
def baseEnd_8301155 : Nat := 1420827500824524808862063

theorem tailTrace_8301155 : CollatzResearch.WordTrace tailWord_8301155 prefixEnd_8301155 1420827500824524808862063 := by
  unfold tailWord_8301155
  simp only [CollatzResearch.WordTrace]
  refine ⟨302767996241340634248304919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201845330827560422832203279 302767996241340634248304919)
  ·
    refine ⟨454151994362010951372457379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302767996241340634248304919 454151994362010951372457379)
    ·
      refine ⟨681227991543016427058686069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454151994362010951372457379 681227991543016427058686069)
      ·
        refine ⟨63865124207157790036751819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 681227991543016427058686069 63865124207157790036751819)
        ·
          refine ⟨95797686310736685055127729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63865124207157790036751819 95797686310736685055127729)
          ·
            refine ⟨71848264733052513791345797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95797686310736685055127729 71848264733052513791345797)
            ·
              refine ⟨13471549637447346335877337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71848264733052513791345797 13471549637447346335877337)
              ·
                refine ⟨10103662228085509751908003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13471549637447346335877337 10103662228085509751908003)
                ·
                  refine ⟨15155493342128264627862005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103662228085509751908003 15155493342128264627862005)
                  ·
                    refine ⟨1420827500824524808862063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155493342128264627862005 1420827500824524808862063)
                    ·
                      rfl

theorem cell23_8301155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 5].length) (baseStart_8301155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301155 prefixEnd_8301155 := by exact prefixLift 8301155
  have htrace : WordTrace (prefixWord ++ tailWord_8301155) baseStart_8301155 baseEnd_8301155 := by
    simpa [prefixWord, tailWord_8301155, baseEnd_8301155] using wordTrace_append hprefix tailTrace_8301155
  have hstable : (prefixWord ++ tailWord_8301155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301155).length < 2 ^ (prefixWord ++ tailWord_8301155).sum := by decide
  have hdescent : baseEnd_8301155 < baseStart_8301155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301162 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_8301162 : Nat := 118140960795 + 8301162 * 2 ^ 59
def prefixEnd_8301162 : Nat := 4983230072969 + 3 ^ 40 * 8301162 * 2
def baseEnd_8301162 : Nat := 4262486096838155899198657

theorem tailTrace_8301162 : CollatzResearch.WordTrace tailWord_8301162 prefixEnd_8301162 4262486096838155899198657 := by
  unfold tailWord_8301162
  simp only [CollatzResearch.WordTrace]
  refine ⟨75692062888078818610952435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201845501034876849629206493 75692062888078818610952435)
  ·
    refine ⟨113538094332118227916428653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75692062888078818610952435 113538094332118227916428653)
    ·
      refine ⟨42576785374544335468660745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113538094332118227916428653 42576785374544335468660745)
      ·
        refine ⟨31932589030908251601495559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42576785374544335468660745 31932589030908251601495559)
        ·
          refine ⟨47898883546362377402243339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31932589030908251601495559 47898883546362377402243339)
          ·
            refine ⟨71848325319543566103365009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47898883546362377402243339 71848325319543566103365009)
            ·
              refine ⟨53886243989657674577523757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71848325319543566103365009 53886243989657674577523757)
              ·
                refine ⟨20207341496121627966571409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53886243989657674577523757 20207341496121627966571409)
                ·
                  refine ⟨15155506122091220974928557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20207341496121627966571409 15155506122091220974928557)
                  ·
                    refine ⟨5683314795784207865598209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15155506122091220974928557 5683314795784207865598209)
                    ·
                      refine ⟨4262486096838155899198657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683314795784207865598209 4262486096838155899198657)
                      ·
                        rfl

theorem cell23_8301162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_8301162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301162 prefixEnd_8301162 := by exact prefixLift 8301162
  have htrace : WordTrace (prefixWord ++ tailWord_8301162) baseStart_8301162 baseEnd_8301162 := by
    simpa [prefixWord, tailWord_8301162, baseEnd_8301162] using wordTrace_append hprefix tailTrace_8301162
  have hstable : (prefixWord ++ tailWord_8301162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301162).length < 2 ^ (prefixWord ++ tailWord_8301162).sum := by decide
  have hdescent : baseEnd_8301162 < baseStart_8301162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301175 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_8301175 : Nat := 118140960795 + 8301175 * 2 ^ 59
def prefixEnd_8301175 : Nat := 4983230072969 + 3 ^ 40 * 8301175 * 2
def baseEnd_8301175 : Nat := 4262492772086664348336097

theorem tailTrace_8301175 : CollatzResearch.WordTrace tailWord_8301175 prefixEnd_8301175 4262492772086664348336097 := by
  unfold tailWord_8301175
  simp only [CollatzResearch.WordTrace]
  refine ⟨302768725701268177664032979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201845817134178785109355319 302768725701268177664032979)
  ·
    refine ⟨454153088551902266496049469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302768725701268177664032979 454153088551902266496049469)
    ·
      refine ⟨170307408206963349936018551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454153088551902266496049469 170307408206963349936018551)
      ·
        refine ⟨255461112310445024904027827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170307408206963349936018551 255461112310445024904027827)
        ·
          refine ⟨383191668465667537356041741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255461112310445024904027827 383191668465667537356041741)
          ·
            refine ⟨143696875674625326508515653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383191668465667537356041741 143696875674625326508515653)
            ·
              refine ⟨26943164188992248720346685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143696875674625326508515653 26943164188992248720346685)
              ·
                refine ⟨10103686570872093270130007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26943164188992248720346685 10103686570872093270130007)
                ·
                  refine ⟨15155529856308139905195011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103686570872093270130007 15155529856308139905195011)
                  ·
                    refine ⟨22733294784462209857792517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15155529856308139905195011 22733294784462209857792517)
                    ·
                      refine ⟨4262492772086664348336097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22733294784462209857792517 4262492772086664348336097)
                      ·
                        rfl

theorem cell23_8301175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_8301175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301175 prefixEnd_8301175 := by exact prefixLift 8301175
  have htrace : WordTrace (prefixWord ++ tailWord_8301175) baseStart_8301175 baseEnd_8301175 := by
    simpa [prefixWord, tailWord_8301175, baseEnd_8301175] using wordTrace_append hprefix tailTrace_8301175
  have hstable : (prefixWord ++ tailWord_8301175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301175).length < 2 ^ (prefixWord ++ tailWord_8301175).sum := by decide
  have hdescent : baseEnd_8301175 < baseStart_8301175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301178 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_8301178 : Nat := 118140960795 + 8301178 * 2 ^ 59
def prefixEnd_8301178 : Nat := 4983230072969 + 3 ^ 40 * 8301178 * 2
def baseEnd_8301178 : Nat := 4262494312528627836598583

theorem tailTrace_8301178 : CollatzResearch.WordTrace tailWord_8301178 prefixEnd_8301178 4262494312528627836598583 := by
  unfold tailWord_8301178
  simp only [CollatzResearch.WordTrace]
  refine ⟨75692208780064327294098047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201845890080171539450928125 75692208780064327294098047)
  ·
    refine ⟨113538313170096490941147071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75692208780064327294098047 113538313170096490941147071)
    ·
      refine ⟨170307469755144736411720607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113538313170096490941147071 170307469755144736411720607)
      ·
        refine ⟨255461204632717104617580911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170307469755144736411720607 255461204632717104617580911)
        ·
          refine ⟨383191806949075656926371367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255461204632717104617580911 383191806949075656926371367)
          ·
            refine ⟨574787710423613485389557051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383191806949075656926371367 574787710423613485389557051)
            ·
              refine ⟨862181565635420228084335577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574787710423613485389557051 862181565635420228084335577)
              ·
                refine ⟨646636174226565171063251683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862181565635420228084335577 646636174226565171063251683)
                ·
                  refine ⟨969954261339847756594877525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646636174226565171063251683 969954261339847756594877525)
                  ·
                    refine ⟨11366651500076340897596221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 969954261339847756594877525 11366651500076340897596221)
                    ·
                      refine ⟨4262494312528627836598583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11366651500076340897596221 4262494312528627836598583)
                      ·
                        rfl

theorem cell23_8301178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_8301178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301178 prefixEnd_8301178 := by exact prefixLift 8301178
  have htrace : WordTrace (prefixWord ++ tailWord_8301178) baseStart_8301178 baseEnd_8301178 := by
    simpa [prefixWord, tailWord_8301178, baseEnd_8301178] using wordTrace_append hprefix tailTrace_8301178
  have hstable : (prefixWord ++ tailWord_8301178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301178).length < 2 ^ (prefixWord ++ tailWord_8301178).sum := by decide
  have hdescent : baseEnd_8301178 < baseStart_8301178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301185 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_8301185 : Nat := 118140960795 + 8301185 * 2 ^ 59
def prefixEnd_8301185 : Nat := 4983230072969 + 3 ^ 40 * 8301185 * 2
def baseEnd_8301185 : Nat := 1420832635631069769737017

theorem tailTrace_8301185 : CollatzResearch.WordTrace tailWord_8301185 prefixEnd_8301185 1420832635631069769737017 := by
  unfold tailWord_8301185
  simp only [CollatzResearch.WordTrace]
  refine ⟨302769090431231949371897009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201846060287487966247931339 302769090431231949371897009)
  ·
    refine ⟨227076817823423962028922757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302769090431231949371897009 227076817823423962028922757)
    ·
      refine ⟨42576903341891992880423017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227076817823423962028922757 42576903341891992880423017)
      ·
        refine ⟨31932677506418994660317263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42576903341891992880423017 31932677506418994660317263)
        ·
          refine ⟨47899016259628491990475895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31932677506418994660317263 47899016259628491990475895)
          ·
            refine ⟨71848524389442737985713843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47899016259628491990475895 71848524389442737985713843)
            ·
              refine ⟨107772786584164106978570765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71848524389442737985713843 107772786584164106978570765)
              ·
                refine ⟨40414794969061540116964037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107772786584164106978570765 40414794969061540116964037)
                ·
                  refine ⟨7577774056699038771930757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40414794969061540116964037 7577774056699038771930757)
                  ·
                    refine ⟨1420832635631069769737017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577774056699038771930757 1420832635631069769737017)
                    ·
                      rfl

theorem cell23_8301185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_8301185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301185 prefixEnd_8301185 := by exact prefixLift 8301185
  have htrace : WordTrace (prefixWord ++ tailWord_8301185) baseStart_8301185 baseEnd_8301185 := by
    simpa [prefixWord, tailWord_8301185, baseEnd_8301185] using wordTrace_append hprefix tailTrace_8301185
  have hstable : (prefixWord ++ tailWord_8301185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301185).length < 2 ^ (prefixWord ++ tailWord_8301185).sum := by decide
  have hdescent : baseEnd_8301185 < baseStart_8301185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301212 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_8301212 : Nat := 118140960795 + 8301212 * 2 ^ 59
def prefixEnd_8301212 : Nat := 4983230072969 + 3 ^ 40 * 8301212 * 2
def baseEnd_8301212 : Nat := 4262511770870880703573427

theorem tailTrace_8301212 : CollatzResearch.WordTrace tailWord_8301212 prefixEnd_8301212 4262511770870880703573427 := by
  unfold tailWord_8301212
  simp only [CollatzResearch.WordTrace]
  refine ⟨151385037601067066491564945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201846716801422755322086593 151385037601067066491564945)
  ·
    refine ⟨113538778200800299868673709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151385037601067066491564945 113538778200800299868673709)
    ·
      refine ⟨42577041825300112450752641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113538778200800299868673709 42577041825300112450752641)
      ·
        refine ⟨31932781368975084338064481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42577041825300112450752641 31932781368975084338064481)
        ·
          refine ⟨23949586026731313253548361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31932781368975084338064481 23949586026731313253548361)
          ·
            refine ⟨17962189520048484940161271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23949586026731313253548361 17962189520048484940161271)
            ·
              refine ⟨26943284280072727410241907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17962189520048484940161271 26943284280072727410241907)
              ·
                refine ⟨40414926420109091115362861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26943284280072727410241907 40414926420109091115362861)
                ·
                  refine ⟨15155597407540909168261073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40414926420109091115362861 15155597407540909168261073)
                  ·
                    refine ⟨11366698055655681876195805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15155597407540909168261073 11366698055655681876195805)
                    ·
                      refine ⟨4262511770870880703573427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11366698055655681876195805 4262511770870880703573427)
                      ·
                        rfl

theorem cell23_8301212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_8301212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301212 prefixEnd_8301212 := by exact prefixLift 8301212
  have htrace : WordTrace (prefixWord ++ tailWord_8301212) baseStart_8301212 baseEnd_8301212 := by
    simpa [prefixWord, tailWord_8301212, baseEnd_8301212] using wordTrace_append hprefix tailTrace_8301212
  have hstable : (prefixWord ++ tailWord_8301212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301212).length < 2 ^ (prefixWord ++ tailWord_8301212).sum := by decide
  have hdescent : baseEnd_8301212 < baseStart_8301212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301249 : List Nat := [1, 2, 6, 2, 1, 2, 1, 8]
def baseStart_8301249 : Nat := 118140960795 + 8301249 * 2 ^ 59
def prefixEnd_8301249 : Nat := 4983230072969 + 3 ^ 40 * 8301249 * 2
def baseEnd_8301249 : Nat := 157871509987225816992991

theorem tailTrace_8301249 : CollatzResearch.WordTrace tailWord_8301249 prefixEnd_8301249 157871509987225816992991 := by
  unfold tailWord_8301249
  simp only [CollatzResearch.WordTrace]
  refine ⟨302771424703000088302226801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201847616468666725534817867 302771424703000088302226801)
  ·
    refine ⟨227078568527250066226670101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302771424703000088302226801 227078568527250066226670101)
    ·
      refine ⟨10644307899714846854375161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227078568527250066226670101 10644307899714846854375161)
      ·
        refine ⟨7983230924786135140781371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10644307899714846854375161 7983230924786135140781371)
        ·
          refine ⟨11974846387179202711172057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983230924786135140781371 11974846387179202711172057)
          ·
            refine ⟨8981134790384402033379043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11974846387179202711172057 8981134790384402033379043)
            ·
              refine ⟨13471702185576603050068565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981134790384402033379043 13471702185576603050068565)
              ·
                refine ⟨157871509987225816992991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13471702185576603050068565 157871509987225816992991)
                ·
                  rfl

theorem cell23_8301249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 8].length) (baseStart_8301249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301249 prefixEnd_8301249 := by exact prefixLift 8301249
  have htrace : WordTrace (prefixWord ++ tailWord_8301249) baseStart_8301249 baseEnd_8301249 := by
    simpa [prefixWord, tailWord_8301249, baseEnd_8301249] using wordTrace_append hprefix tailTrace_8301249
  have hstable : (prefixWord ++ tailWord_8301249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301249).length < 2 ^ (prefixWord ++ tailWord_8301249).sum := by decide
  have hdescent : baseEnd_8301249 < baseStart_8301249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301295 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_8301295 : Nat := 118140960795 + 8301295 * 2 ^ 59
def prefixEnd_8301295 : Nat := 4983230072969 + 3 ^ 40 * 8301295 * 2
def baseEnd_8301295 : Nat := 4262554389765203878835545

theorem tailTrace_8301295 : CollatzResearch.WordTrace tailWord_8301295 prefixEnd_8301295 4262554389765203878835545 := by
  unfold tailWord_8301295
  simp only [CollatzResearch.WordTrace]
  refine ⟨302773102460833438158401339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201848734973888958772267559 302773102460833438158401339)
  ·
    refine ⟨454159653691250157237602009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302773102460833438158401339 454159653691250157237602009)
    ·
      refine ⟨340619740268437617928201507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454159653691250157237602009 340619740268437617928201507)
      ·
        refine ⟨510929610402656426892302261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340619740268437617928201507 510929610402656426892302261)
        ·
          refine ⟨47899650975249040021153337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510929610402656426892302261 47899650975249040021153337)
          ·
            refine ⟨35924738231436780015865003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47899650975249040021153337 35924738231436780015865003)
            ·
              refine ⟨53887107347155170023797505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35924738231436780015865003 53887107347155170023797505)
              ·
                refine ⟨40415330510366377517848129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53887107347155170023797505 40415330510366377517848129)
                ·
                  refine ⟨30311497882774783138386097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40415330510366377517848129 30311497882774783138386097)
                  ·
                    refine ⟨22733623412081087353789573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30311497882774783138386097 22733623412081087353789573)
                    ·
                      refine ⟨4262554389765203878835545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22733623412081087353789573 4262554389765203878835545)
                      ·
                        rfl

theorem cell23_8301295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_8301295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301295 prefixEnd_8301295 := by exact prefixLift 8301295
  have htrace : WordTrace (prefixWord ++ tailWord_8301295) baseStart_8301295 baseEnd_8301295 := by
    simpa [prefixWord, tailWord_8301295, baseEnd_8301295] using wordTrace_append hprefix tailTrace_8301295
  have hstable : (prefixWord ++ tailWord_8301295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301295).length < 2 ^ (prefixWord ++ tailWord_8301295).sum := by decide
  have hdescent : baseEnd_8301295 < baseStart_8301295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301345 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_8301345 : Nat := 118140960795 + 8301345 * 2 ^ 59
def prefixEnd_8301345 : Nat := 4983230072969 + 3 ^ 40 * 8301345 * 2
def baseEnd_8301345 : Nat := 4262580063797928683210315

theorem tailTrace_8301345 : CollatzResearch.WordTrace tailWord_8301345 prefixEnd_8301345 4262580063797928683210315 := by
  unfold tailWord_8301345
  simp only [CollatzResearch.WordTrace]
  refine ⟨302774926110652296697721489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201849950740434864465147659 302774926110652296697721489)
  ·
    refine ⟨227081194582989222523291117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302774926110652296697721489 227081194582989222523291117)
    ·
      refine ⟨85155447968620958446234169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227081194582989222523291117 85155447968620958446234169)
      ·
        refine ⟨63866585976465718834675627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85155447968620958446234169 63866585976465718834675627)
        ·
          refine ⟨95799878964698578252013441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63866585976465718834675627 95799878964698578252013441)
          ·
            refine ⟨71849909223523933689010081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95799878964698578252013441 71849909223523933689010081)
            ·
              refine ⟨53887431917642950266757561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71849909223523933689010081 53887431917642950266757561)
              ·
                refine ⟨40415573938232212700068171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53887431917642950266757561 40415573938232212700068171)
                ·
                  refine ⟨60623360907348319050102257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40415573938232212700068171 60623360907348319050102257)
                  ·
                    refine ⟨45467520680511239287576693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60623360907348319050102257 45467520680511239287576693)
                    ·
                      refine ⟨4262580063797928683210315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45467520680511239287576693 4262580063797928683210315)
                      ·
                        rfl

theorem cell23_8301345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_8301345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301345 prefixEnd_8301345 := by exact prefixLift 8301345
  have htrace : WordTrace (prefixWord ++ tailWord_8301345) baseStart_8301345 baseEnd_8301345 := by
    simpa [prefixWord, tailWord_8301345, baseEnd_8301345] using wordTrace_append hprefix tailTrace_8301345
  have hstable : (prefixWord ++ tailWord_8301345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301345).length < 2 ^ (prefixWord ++ tailWord_8301345).sum := by decide
  have hdescent : baseEnd_8301345 < baseStart_8301345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301352 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_8301352 : Nat := 118140960795 + 8301352 * 2 ^ 59
def prefixEnd_8301352 : Nat := 4983230072969 + 3 ^ 40 * 8301352 * 2
def baseEnd_8301352 : Nat := 1420861219387503385274261

theorem tailTrace_8301352 : CollatzResearch.WordTrace tailWord_8301352 prefixEnd_8301352 1420861219387503385274261 := by
  unfold tailWord_8301352
  simp only [CollatzResearch.WordTrace]
  refine ⟨151387590710813468446613155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201850120947751291262150873 151387590710813468446613155)
  ·
    refine ⟨227081386066220202669919733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151387590710813468446613155 227081386066220202669919733)
    ·
      refine ⟨21288879943708144000304975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227081386066220202669919733 21288879943708144000304975)
      ·
        refine ⟨31933319915562216000457463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21288879943708144000304975 31933319915562216000457463)
        ·
          refine ⟨47899979873343324000686195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31933319915562216000457463 47899979873343324000686195)
          ·
            refine ⟨71849969810014986001029293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47899979873343324000686195 71849969810014986001029293)
            ·
              refine ⟨26943738678755619750385985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71849969810014986001029293 26943738678755619750385985)
              ·
                refine ⟨20207804009066714812789489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26943738678755619750385985 20207804009066714812789489)
                ·
                  refine ⟨15155853006800036109592117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20207804009066714812789489 15155853006800036109592117)
                  ·
                    refine ⟨1420861219387503385274261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15155853006800036109592117 1420861219387503385274261)
                    ·
                      rfl

theorem cell23_8301352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_8301352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301352 prefixEnd_8301352 := by exact prefixLift 8301352
  have htrace : WordTrace (prefixWord ++ tailWord_8301352) baseStart_8301352 baseEnd_8301352 := by
    simpa [prefixWord, tailWord_8301352, baseEnd_8301352] using wordTrace_append hprefix tailTrace_8301352
  have hstable : (prefixWord ++ tailWord_8301352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301352).length < 2 ^ (prefixWord ++ tailWord_8301352).sum := by decide
  have hdescent : baseEnd_8301352 < baseStart_8301352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301355 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4]
def baseStart_8301355 : Nat := 118140960795 + 8301355 * 2 ^ 59
def prefixEnd_8301355 : Nat := 4983230072969 + 3 ^ 40 * 8301355 * 2
def baseEnd_8301355 : Nat := 4262585198604473644085269

theorem tailTrace_8301355 : CollatzResearch.WordTrace tailWord_8301355 prefixEnd_8301355 4262585198604473644085269 := by
  unfold tailWord_8301355
  simp only [CollatzResearch.WordTrace]
  refine ⟨302775290840616068405585519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201850193893744045603723679 302775290840616068405585519)
  ·
    refine ⟨454162936260924102608378279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302775290840616068405585519 454162936260924102608378279)
    ·
      refine ⟨681244404391386153912567419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454162936260924102608378279 681244404391386153912567419)
      ·
        refine ⟨1021866606587079230868851129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681244404391386153912567419 1021866606587079230868851129)
        ·
          refine ⟨766399954940309423151638347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021866606587079230868851129 766399954940309423151638347)
          ·
            refine ⟨1149599932410464134727457521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766399954940309423151638347 1149599932410464134727457521)
            ·
              refine ⟨862199949307848101045593141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149599932410464134727457521 862199949307848101045593141)
              ·
                refine ⟨80831245247610759473024357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 862199949307848101045593141 80831245247610759473024357)
                ·
                  refine ⟨15155858483927017401192067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80831245247610759473024357 15155858483927017401192067)
                  ·
                    refine ⟨22733787725890526101788101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15155858483927017401192067 22733787725890526101788101)
                    ·
                      refine ⟨4262585198604473644085269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22733787725890526101788101 4262585198604473644085269)
                      ·
                        rfl

theorem cell23_8301355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4].length) (baseStart_8301355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301355 prefixEnd_8301355 := by exact prefixLift 8301355
  have htrace : WordTrace (prefixWord ++ tailWord_8301355) baseStart_8301355 baseEnd_8301355 := by
    simpa [prefixWord, tailWord_8301355, baseEnd_8301355] using wordTrace_append hprefix tailTrace_8301355
  have hstable : (prefixWord ++ tailWord_8301355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301355).length < 2 ^ (prefixWord ++ tailWord_8301355).sum := by decide
  have hdescent : baseEnd_8301355 < baseStart_8301355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301372 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_8301372 : Nat := 118140960795 + 8301372 * 2 ^ 59
def prefixEnd_8301372 : Nat := 4983230072969 + 3 ^ 40 * 8301372 * 2
def baseEnd_8301372 : Nat := 4262593927775600077572691

theorem tailTrace_8301372 : CollatzResearch.WordTrace tailWord_8301372 prefixEnd_8301372 4262593927775600077572691 := by
  unfold tailWord_8301372
  simp only [CollatzResearch.WordTrace]
  refine ⟨151387955440777240154477185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201850607254369653539302913 151387955440777240154477185)
  ·
    refine ⟨113540966580582930115857889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151387955440777240154477185 113540966580582930115857889)
    ·
      refine ⟨85155724935437197586893417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113540966580582930115857889 85155724935437197586893417)
      ·
        refine ⟨63866793701577898190170063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85155724935437197586893417 63866793701577898190170063)
        ·
          refine ⟨95800190552366847285255095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63866793701577898190170063 95800190552366847285255095)
          ·
            refine ⟨143700285828550270927882643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95800190552366847285255095 143700285828550270927882643)
            ·
              refine ⟨215550428742825406391823965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143700285828550270927882643 215550428742825406391823965)
              ·
                refine ⟨80831410778559527396933987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215550428742825406391823965 80831410778559527396933987)
                ·
                  refine ⟨121247116167839291095400981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80831410778559527396933987 121247116167839291095400981)
                  ·
                    refine ⟨5683458570367466770096921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121247116167839291095400981 5683458570367466770096921)
                    ·
                      refine ⟨4262593927775600077572691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683458570367466770096921 4262593927775600077572691)
                      ·
                        rfl

theorem cell23_8301372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_8301372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301372 prefixEnd_8301372 := by exact prefixLift 8301372
  have htrace : WordTrace (prefixWord ++ tailWord_8301372) baseStart_8301372 baseEnd_8301372 := by
    simpa [prefixWord, tailWord_8301372, baseEnd_8301372] using wordTrace_append hprefix tailTrace_8301372
  have hstable : (prefixWord ++ tailWord_8301372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301372).length < 2 ^ (prefixWord ++ tailWord_8301372).sum := by decide
  have hdescent : baseEnd_8301372 < baseStart_8301372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301392 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_8301392 : Nat := 118140960795 + 8301392 * 2 ^ 59
def prefixEnd_8301392 : Nat := 4983230072969 + 3 ^ 40 * 8301392 * 2
def baseEnd_8301392 : Nat := 4262604197388689999322599

theorem tailTrace_8301392 : CollatzResearch.WordTrace tailWord_8301392 prefixEnd_8301392 4262604197388689999322599 := by
  unfold tailWord_8301392
  simp only [CollatzResearch.WordTrace]
  refine ⟨151388320170741011862341215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201851093560988015816454953 151388320170741011862341215)
  ·
    refine ⟨227082480256111517793511823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151388320170741011862341215 227082480256111517793511823)
    ·
      refine ⟨340623720384167276690267735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227082480256111517793511823 340623720384167276690267735)
      ·
        refine ⟨510935580576250915035401603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340623720384167276690267735 510935580576250915035401603)
        ·
          refine ⟨766403370864376372553102405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510935580576250915035401603 766403370864376372553102405)
          ·
            refine ⟨143700632037070569853706701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 766403370864376372553102405 143700632037070569853706701)
            ·
              refine ⟨53887737013901463695140013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143700632037070569853706701 53887737013901463695140013)
              ·
                refine ⟨20207901380213048885677505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53887737013901463695140013 20207901380213048885677505)
                ·
                  refine ⟨15155926035159786664258129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20207901380213048885677505 15155926035159786664258129)
                  ·
                    refine ⟨11366944526369839998193597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15155926035159786664258129 11366944526369839998193597)
                    ·
                      refine ⟨4262604197388689999322599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11366944526369839998193597 4262604197388689999322599)
                      ·
                        rfl

theorem cell23_8301392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_8301392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301392 prefixEnd_8301392 := by exact prefixLift 8301392
  have htrace : WordTrace (prefixWord ++ tailWord_8301392) baseStart_8301392 baseEnd_8301392 := by
    simpa [prefixWord, tailWord_8301392, baseEnd_8301392] using wordTrace_append hprefix tailTrace_8301392
  have hstable : (prefixWord ++ tailWord_8301392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301392).length < 2 ^ (prefixWord ++ tailWord_8301392).sum := by decide
  have hdescent : baseEnd_8301392 < baseStart_8301392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301412 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 6]
def baseStart_8301412 : Nat := 118140960795 + 8301412 * 2 ^ 59
def prefixEnd_8301412 : Nat := 4983230072969 + 3 ^ 40 * 8301412 * 2
def baseEnd_8301412 : Nat := 473623829666864435674723

theorem tailTrace_8301412 : CollatzResearch.WordTrace tailWord_8301412 prefixEnd_8301412 473623829666864435674723 := by
  unfold tailWord_8301412
  simp only [CollatzResearch.WordTrace]
  refine ⟨151388684900704783570205245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201851579867606378093606993 151388684900704783570205245)
  ·
    refine ⟨56770756837764293838826967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151388684900704783570205245 56770756837764293838826967)
    ·
      refine ⟨85156135256646440758240451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56770756837764293838826967 85156135256646440758240451)
      ·
        refine ⟨127734202884969661137360677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85156135256646440758240451 127734202884969661137360677)
        ·
          refine ⟨23950163040931811463255127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127734202884969661137360677 23950163040931811463255127)
          ·
            refine ⟨35925244561397717194882691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23950163040931811463255127 35925244561397717194882691)
            ·
              refine ⟨53887866842096575792324037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35925244561397717194882691 53887866842096575792324037)
              ·
                refine ⟨10103975032893107961060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53887866842096575792324037 10103975032893107961060757)
                ·
                  refine ⟨473623829666864435674723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10103975032893107961060757 473623829666864435674723)
                  ·
                    rfl

theorem cell23_8301412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_8301412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301412 prefixEnd_8301412 := by exact prefixLift 8301412
  have htrace : WordTrace (prefixWord ++ tailWord_8301412) baseStart_8301412 baseEnd_8301412 := by
    simpa [prefixWord, tailWord_8301412, baseEnd_8301412] using wordTrace_append hprefix tailTrace_8301412
  have hstable : (prefixWord ++ tailWord_8301412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301412).length < 2 ^ (prefixWord ++ tailWord_8301412).sum := by decide
  have hdescent : baseEnd_8301412 < baseStart_8301412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301416 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 1, 4]
def baseStart_8301416 : Nat := 118140960795 + 8301416 * 2 ^ 59
def prefixEnd_8301416 : Nat := 4983230072969 + 3 ^ 40 * 8301416 * 2
def baseEnd_8301416 : Nat := 1420872173641465968474163

theorem tailTrace_8301416 : CollatzResearch.WordTrace tailWord_8301416 prefixEnd_8301416 1420872173641465968474163 := by
  unfold tailWord_8301416
  simp only [CollatzResearch.WordTrace]
  refine ⟨151388757846697537911778051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201851677128930050549037401 151388757846697537911778051)
  ·
    refine ⟨227083136770046306867667077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151388757846697537911778051 227083136770046306867667077)
    ·
      refine ⟨42578088144383682537687577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227083136770046306867667077 42578088144383682537687577)
      ·
        refine ⟨31933566108287761903265683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42578088144383682537687577 31933566108287761903265683)
        ·
          refine ⟨47900349162431642854898525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31933566108287761903265683 47900349162431642854898525)
          ·
            refine ⟨17962630935911866070586947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47900349162431642854898525 17962630935911866070586947)
            ·
              refine ⟨26943946403867799105880421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17962630935911866070586947 26943946403867799105880421)
              ·
                refine ⟨5051989950725212332352579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26943946403867799105880421 5051989950725212332352579)
                ·
                  refine ⟨7577984926087818498528869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051989950725212332352579 7577984926087818498528869)
                  ·
                    refine ⟨1420872173641465968474163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577984926087818498528869 1420872173641465968474163)
                    ·
                      rfl

theorem cell23_8301416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_8301416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301416 prefixEnd_8301416 := by exact prefixLift 8301416
  have htrace : WordTrace (prefixWord ++ tailWord_8301416) baseStart_8301416 baseEnd_8301416 := by
    simpa [prefixWord, tailWord_8301416, baseEnd_8301416] using wordTrace_append hprefix tailTrace_8301416
  have hstable : (prefixWord ++ tailWord_8301416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301416).length < 2 ^ (prefixWord ++ tailWord_8301416).sum := by decide
  have hdescent : baseEnd_8301416 < baseStart_8301416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301449 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 5, 2]
def baseStart_8301449 : Nat := 118140960795 + 8301449 * 2 ^ 59
def prefixEnd_8301449 : Nat := 4983230072969 + 3 ^ 40 * 8301449 * 2
def baseEnd_8301449 : Nat := 4262633465785996276309837

theorem tailTrace_8301449 : CollatzResearch.WordTrace tailWord_8301449 prefixEnd_8301449 4262633465785996276309837 := by
  unfold tailWord_8301449
  simp only [CollatzResearch.WordTrace]
  refine ⟨302778719302275522459507401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201852479534850348306338267 302778719302275522459507401)
  ·
    refine ⟨227084039476706641844630551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302778719302275522459507401 227084039476706641844630551)
    ·
      refine ⟨340626059215059962766945827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227084039476706641844630551 340626059215059962766945827)
      ·
        refine ⟨510939088822589944150418741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340626059215059962766945827 510939088822589944150418741)
        ·
          refine ⟨47900539577117807264101757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510939088822589944150418741 47900539577117807264101757)
          ·
            refine ⟨17962702341419177724038159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47900539577117807264101757 17962702341419177724038159)
            ·
              refine ⟨26944053512128766586057239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17962702341419177724038159 26944053512128766586057239)
              ·
                refine ⟨40416080268193149879085859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26944053512128766586057239 40416080268193149879085859)
                ·
                  refine ⟨60624120402289724818628789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40416080268193149879085859 60624120402289724818628789)
                  ·
                    refine ⟨5683511287714661701746449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60624120402289724818628789 5683511287714661701746449)
                    ·
                      refine ⟨4262633465785996276309837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683511287714661701746449 4262633465785996276309837)
                      ·
                        rfl

theorem cell23_8301449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 5, 2].length) (baseStart_8301449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301449 prefixEnd_8301449 := by exact prefixLift 8301449
  have htrace : WordTrace (prefixWord ++ tailWord_8301449) baseStart_8301449 baseEnd_8301449 := by
    simpa [prefixWord, tailWord_8301449, baseEnd_8301449] using wordTrace_append hprefix tailTrace_8301449
  have hstable : (prefixWord ++ tailWord_8301449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301449).length < 2 ^ (prefixWord ++ tailWord_8301449).sum := by decide
  have hdescent : baseEnd_8301449 < baseStart_8301449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301473 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_8301473 : Nat := 118140960795 + 8301473 * 2 ^ 59
def prefixEnd_8301473 : Nat := 4983230072969 + 3 ^ 40 * 8301473 * 2
def baseEnd_8301473 : Nat := 4262645789321704182409727

theorem tailTrace_8301473 : CollatzResearch.WordTrace tailWord_8301473 prefixEnd_8301473 4262645789321704182409727 := by
  unfold tailWord_8301473
  simp only [CollatzResearch.WordTrace]
  refine ⟨302779594654188574558381073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201853063102792383038920715 302779594654188574558381073)
  ·
    refine ⟨227084695990641430918785805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302779594654188574558381073 227084695990641430918785805)
    ·
      refine ⟨85156760996490536594544677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227084695990641430918785805 85156760996490536594544677)
      ·
        refine ⟨15966892686841975611477127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85156760996490536594544677 15966892686841975611477127)
        ·
          refine ⟨23950339030262963417215691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15966892686841975611477127 23950339030262963417215691)
          ·
            refine ⟨35925508545394445125823537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23950339030262963417215691 35925508545394445125823537)
            ·
              refine ⟨26944131409045833844367653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35925508545394445125823537 26944131409045833844367653)
              ·
                refine ⟨5052024639196093845818935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26944131409045833844367653 5052024639196093845818935)
                ·
                  refine ⟨7578036958794140768728403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052024639196093845818935 7578036958794140768728403)
                  ·
                    refine ⟨11367055438191211153092605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7578036958794140768728403 11367055438191211153092605)
                    ·
                      refine ⟨4262645789321704182409727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367055438191211153092605 4262645789321704182409727)
                      ·
                        rfl

theorem cell23_8301473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_8301473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301473 prefixEnd_8301473 := by exact prefixLift 8301473
  have htrace : WordTrace (prefixWord ++ tailWord_8301473) baseStart_8301473 baseEnd_8301473 := by
    simpa [prefixWord, tailWord_8301473, baseEnd_8301473] using wordTrace_append hprefix tailTrace_8301473
  have hstable : (prefixWord ++ tailWord_8301473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301473).length < 2 ^ (prefixWord ++ tailWord_8301473).sum := by decide
  have hdescent : baseEnd_8301473 < baseStart_8301473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301496 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_8301496 : Nat := 118140960795 + 8301496 * 2 ^ 59
def prefixEnd_8301496 : Nat := 4983230072969 + 3 ^ 40 * 8301496 * 2
def baseEnd_8301496 : Nat := 4262657599376757592422121

theorem tailTrace_8301496 : CollatzResearch.WordTrace tailWord_8301496 prefixEnd_8301496 4262657599376757592422121 := by
  unfold tailWord_8301496
  simp only [CollatzResearch.WordTrace]
  refine ⟨151390216766552624743234171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201853622355403499657645561 151390216766552624743234171)
  ·
    refine ⟨227085325149828937114851257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151390216766552624743234171 227085325149828937114851257)
    ·
      refine ⟨170313993862371702836138443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227085325149828937114851257 170313993862371702836138443)
      ·
        refine ⟨255470990793557554254207665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170313993862371702836138443 255470990793557554254207665)
        ·
          refine ⟨191603243095168165690655749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255470990793557554254207665 191603243095168165690655749)
          ·
            refine ⟨35925608080344031066997953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191603243095168165690655749 35925608080344031066997953)
            ·
              refine ⟨26944206060258023300248465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35925608080344031066997953 26944206060258023300248465)
              ·
                refine ⟨20208154545193517475186349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26944206060258023300248465 20208154545193517475186349)
                ·
                  refine ⟨7578057954447569053194881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20208154545193517475186349 7578057954447569053194881)
                  ·
                    refine ⟨5683543465835676789896161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578057954447569053194881 5683543465835676789896161)
                    ·
                      refine ⟨4262657599376757592422121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683543465835676789896161 4262657599376757592422121)
                      ·
                        rfl

theorem cell23_8301496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_8301496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301496 prefixEnd_8301496 := by exact prefixLift 8301496
  have htrace : WordTrace (prefixWord ++ tailWord_8301496) baseStart_8301496 baseEnd_8301496 := by
    simpa [prefixWord, tailWord_8301496, baseEnd_8301496] using wordTrace_append hprefix tailTrace_8301496
  have hstable : (prefixWord ++ tailWord_8301496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301496).length < 2 ^ (prefixWord ++ tailWord_8301496).sum := by decide
  have hdescent : baseEnd_8301496 < baseStart_8301496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301502 : List Nat := [4, 2, 1, 1, 1, 2, 3, 9]
def baseStart_8301502 : Nat := 118140960795 + 8301502 * 2 ^ 59
def prefixEnd_8301502 : Nat := 4983230072969 + 3 ^ 40 * 8301502 * 2
def baseEnd_8301502 : Nat := 157876321491136465516559

theorem tailTrace_8301502 : CollatzResearch.WordTrace tailWord_8301502 prefixEnd_8301502 157876321491136465516559 := by
  unfold tailWord_8301502
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847581546385439063898345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201853768247389008340791173 37847581546385439063898345)
  ·
    refine ⟨28385686159789079297923759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37847581546385439063898345 28385686159789079297923759)
    ·
      refine ⟨42578529239683618946885639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28385686159789079297923759 42578529239683618946885639)
      ·
        refine ⟨63867793859525428420328459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42578529239683618946885639 63867793859525428420328459)
        ·
          refine ⟨95801690789288142630492689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63867793859525428420328459 95801690789288142630492689)
          ·
            refine ⟨71851268091966106972869517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95801690789288142630492689 71851268091966106972869517)
            ·
              refine ⟨26944225534487290114826069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71851268091966106972869517 26944225534487290114826069)
              ·
                refine ⟨157876321491136465516559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26944225534487290114826069 157876321491136465516559)
                ·
                  rfl

theorem cell23_8301502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_8301502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301502 prefixEnd_8301502 := by exact prefixLift 8301502
  have htrace : WordTrace (prefixWord ++ tailWord_8301502) baseStart_8301502 baseEnd_8301502 := by
    simpa [prefixWord, tailWord_8301502, baseEnd_8301502] using wordTrace_append hprefix tailTrace_8301502
  have hstable : (prefixWord ++ tailWord_8301502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301502).length < 2 ^ (prefixWord ++ tailWord_8301502).sum := by decide
  have hdescent : baseEnd_8301502 < baseStart_8301502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301517 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_8301517 : Nat := 118140960795 + 8301517 * 2 ^ 59
def prefixEnd_8301517 : Nat := 4983230072969 + 3 ^ 40 * 8301517 * 2
def baseEnd_8301517 : Nat := 4262668382470502010259525

theorem tailTrace_8301517 : CollatzResearch.WordTrace tailWord_8301517 prefixEnd_8301517 4262668382470502010259525 := by
  unfold tailWord_8301517
  simp only [CollatzResearch.WordTrace]
  refine ⟨302781199466029170072982805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201854132977352780048655203 302781199466029170072982805)
  ·
    refine ⟨14192868724970117347171069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302781199466029170072982805 14192868724970117347171069)
    ·
      refine ⟨5322325771863794005189151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14192868724970117347171069 5322325771863794005189151)
      ·
        refine ⟨7983488657795691007783727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322325771863794005189151 7983488657795691007783727)
        ·
          refine ⟨11975232986693536511675591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983488657795691007783727 11975232986693536511675591)
          ·
            refine ⟨17962849480040304767513387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11975232986693536511675591 17962849480040304767513387)
            ·
              refine ⟨26944274220060457151270081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17962849480040304767513387 26944274220060457151270081)
              ·
                refine ⟨20208205665045342863452561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26944274220060457151270081 20208205665045342863452561)
                ·
                  refine ⟨15156154248784007147589421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20208205665045342863452561 15156154248784007147589421)
                  ·
                    refine ⟨5683557843294002680346033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15156154248784007147589421 5683557843294002680346033)
                    ·
                      refine ⟨4262668382470502010259525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683557843294002680346033 4262668382470502010259525)
                      ·
                        rfl

theorem cell23_8301517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_8301517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301517 prefixEnd_8301517 := by exact prefixLift 8301517
  have htrace : WordTrace (prefixWord ++ tailWord_8301517) baseStart_8301517 baseEnd_8301517 := by
    simpa [prefixWord, tailWord_8301517, baseEnd_8301517] using wordTrace_append hprefix tailTrace_8301517
  have hstable : (prefixWord ++ tailWord_8301517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301517).length < 2 ^ (prefixWord ++ tailWord_8301517).sum := by decide
  have hdescent : baseEnd_8301517 < baseStart_8301517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301550 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_8301550 : Nat := 118140960795 + 8301550 * 2 ^ 59
def prefixEnd_8301550 : Nat := 4983230072969 + 3 ^ 40 * 8301550 * 2
def baseEnd_8301550 : Nat := 4262685327332100381146873

theorem tailTrace_8301550 : CollatzResearch.WordTrace tailWord_8301550 prefixEnd_8301550 4262685327332100381146873 := by
  unfold tailWord_8301550
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847800384363702088616763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201854935383273077805956069 37847800384363702088616763)
  ·
    refine ⟨56771700576545553132925145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37847800384363702088616763 56771700576545553132925145)
    ·
      refine ⟨42578775432409164849693859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56771700576545553132925145 42578775432409164849693859)
      ·
        refine ⟨63868163148613747274540789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42578775432409164849693859 63868163148613747274540789)
        ·
          refine ⟨5987640295182538806988199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63868163148613747274540789 5987640295182538806988199)
          ·
            refine ⟨8981460442773808210482299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987640295182538806988199 8981460442773808210482299)
            ·
              refine ⟨13472190664160712315723449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981460442773808210482299 13472190664160712315723449)
              ·
                refine ⟨10104142998120534236792587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13472190664160712315723449 10104142998120534236792587)
                ·
                  refine ⟨15156214497180801355188881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104142998120534236792587 15156214497180801355188881)
                  ·
                    refine ⟨11367160872885601016391661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15156214497180801355188881 11367160872885601016391661)
                    ·
                      refine ⟨4262685327332100381146873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367160872885601016391661 4262685327332100381146873)
                      ·
                        rfl

theorem cell23_8301550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_8301550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301550 prefixEnd_8301550 := by exact prefixLift 8301550
  have htrace : WordTrace (prefixWord ++ tailWord_8301550) baseStart_8301550 baseEnd_8301550 := by
    simpa [prefixWord, tailWord_8301550, baseEnd_8301550] using wordTrace_append hprefix tailTrace_8301550
  have hstable : (prefixWord ++ tailWord_8301550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301550).length < 2 ^ (prefixWord ++ tailWord_8301550).sum := by decide
  have hdescent : baseEnd_8301550 < baseStart_8301550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301573 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_8301573 : Nat := 118140960795 + 8301573 * 2 ^ 59
def prefixEnd_8301573 : Nat := 4983230072969 + 3 ^ 40 * 8301573 * 2
def baseEnd_8301573 : Nat := 4262697137387153791159267

theorem tailTrace_8301573 : CollatzResearch.WordTrace tailWord_8301573 prefixEnd_8301573 4262697137387153791159267 := by
  unfold tailWord_8301573
  simp only [CollatzResearch.WordTrace]
  refine ⟨302783241953826291637021373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201855494635884194424680915 302783241953826291637021373)
  ·
    refine ⟨113543715732684859363883015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302783241953826291637021373 113543715732684859363883015)
    ·
      refine ⟨170315573599027289045824523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113543715732684859363883015 170315573599027289045824523)
      ·
        refine ⟨255473360398540933568736785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170315573599027289045824523 255473360398540933568736785)
        ·
          refine ⟨191605020298905700176552589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255473360398540933568736785 191605020298905700176552589)
          ·
            refine ⟨71851882612089637566207221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191605020298905700176552589 71851882612089637566207221)
            ·
              refine ⟨6736113994883403521831927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71851882612089637566207221 6736113994883403521831927)
              ·
                refine ⟨10104170992325105282747891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736113994883403521831927 10104170992325105282747891)
                ·
                  refine ⟨15156256488487657924121837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104170992325105282747891 15156256488487657924121837)
                  ·
                    refine ⟨5683596183182871721545689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15156256488487657924121837 5683596183182871721545689)
                    ·
                      refine ⟨4262697137387153791159267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683596183182871721545689 4262697137387153791159267)
                      ·
                        rfl

theorem cell23_8301573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_8301573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301573 prefixEnd_8301573 := by exact prefixLift 8301573
  have htrace : WordTrace (prefixWord ++ tailWord_8301573) baseStart_8301573 baseEnd_8301573 := by
    simpa [prefixWord, tailWord_8301573, baseEnd_8301573] using wordTrace_append hprefix tailTrace_8301573
  have hstable : (prefixWord ++ tailWord_8301573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301573).length < 2 ^ (prefixWord ++ tailWord_8301573).sum := by decide
  have hdescent : baseEnd_8301573 < baseStart_8301573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301589 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_8301589 : Nat := 118140960795 + 8301589 * 2 ^ 59
def prefixEnd_8301589 : Nat := 4983230072969 + 3 ^ 40 * 8301589 * 2
def baseEnd_8301589 : Nat := 4262705353077625728559193

theorem tailTrace_8301589 : CollatzResearch.WordTrace tailWord_8301589 prefixEnd_8301589 4262705353077625728559193 := by
  unfold tailWord_8301589
  simp only [CollatzResearch.WordTrace]
  refine ⟨302783825521768326369603821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201855883681178884246402547 302783825521768326369603821)
  ·
    refine ⟨113543934570663122388601433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302783825521768326369603821 113543934570663122388601433)
    ·
      refine ⟨85157950927997341791451075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113543934570663122388601433 85157950927997341791451075)
      ·
        refine ⟨127736926391996012687176613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85157950927997341791451075 127736926391996012687176613)
        ·
          refine ⟨23950673698499252378845615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127736926391996012687176613 23950673698499252378845615)
          ·
            refine ⟨35926010547748878568268423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23950673698499252378845615 35926010547748878568268423)
            ·
              refine ⟨53889015821623317852402635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35926010547748878568268423 53889015821623317852402635)
              ·
                refine ⟨80833523732434976778603953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53889015821623317852402635 80833523732434976778603953)
                ·
                  refine ⟨60625142799326232583952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80833523732434976778603953 60625142799326232583952965)
                  ·
                    refine ⟨11367214274873668609491181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60625142799326232583952965 11367214274873668609491181)
                    ·
                      refine ⟨4262705353077625728559193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367214274873668609491181 4262705353077625728559193)
                      ·
                        rfl

theorem cell23_8301589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_8301589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301589 prefixEnd_8301589 := by exact prefixLift 8301589
  have htrace : WordTrace (prefixWord ++ tailWord_8301589) baseStart_8301589 baseEnd_8301589 := by
    simpa [prefixWord, tailWord_8301589, baseEnd_8301589] using wordTrace_append hprefix tailTrace_8301589
  have hstable : (prefixWord ++ tailWord_8301589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301589).length < 2 ^ (prefixWord ++ tailWord_8301589).sum := by decide
  have hdescent : baseEnd_8301589 < baseStart_8301589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301599 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_8301599 : Nat := 118140960795 + 8301599 * 2 ^ 59
def prefixEnd_8301599 : Nat := 4983230072969 + 3 ^ 40 * 8301599 * 2
def baseEnd_8301599 : Nat := 4262710487884170689434147

theorem tailTrace_8301599 : CollatzResearch.WordTrace tailWord_8301599 prefixEnd_8301599 4262710487884170689434147 := by
  unfold tailWord_8301599
  simp only [CollatzResearch.WordTrace]
  refine ⟨302784190251732098077467851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201856126834488065384978567 302784190251732098077467851)
  ·
    refine ⟨454176285377598147116201777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302784190251732098077467851 454176285377598147116201777)
    ·
      refine ⟨340632214033198610337151333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454176285377598147116201777 340632214033198610337151333)
      ·
        refine ⟨63868540131224739438215875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340632214033198610337151333 63868540131224739438215875)
        ·
          refine ⟨95802810196837109157323813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63868540131224739438215875 95802810196837109157323813)
          ·
            refine ⟨17963026911906957966998215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95802810196837109157323813 17963026911906957966998215)
            ·
              refine ⟨26944540367860436950497323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17963026911906957966998215 26944540367860436950497323)
              ·
                refine ⟨40416810551790655425745985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26944540367860436950497323 40416810551790655425745985)
                ·
                  refine ⟨30312607913842991569309489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40416810551790655425745985 30312607913842991569309489)
                  ·
                    refine ⟨22734455935382243676982117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30312607913842991569309489 22734455935382243676982117)
                    ·
                      refine ⟨4262710487884170689434147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22734455935382243676982117 4262710487884170689434147)
                      ·
                        rfl

theorem cell23_8301599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_8301599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301599 prefixEnd_8301599 := by exact prefixLift 8301599
  have htrace : WordTrace (prefixWord ++ tailWord_8301599) baseStart_8301599 baseEnd_8301599 := by
    simpa [prefixWord, tailWord_8301599, baseEnd_8301599] using wordTrace_append hprefix tailTrace_8301599
  have hstable : (prefixWord ++ tailWord_8301599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301599).length < 2 ^ (prefixWord ++ tailWord_8301599).sum := by decide
  have hdescent : baseEnd_8301599 < baseStart_8301599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301603 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 2, 2, 2]
def baseStart_8301603 : Nat := 118140960795 + 8301603 * 2 ^ 59
def prefixEnd_8301603 : Nat := 4983230072969 + 3 ^ 40 * 8301603 * 2
def baseEnd_8301603 : Nat := 4262712541806788673784129

theorem tailTrace_8301603 : CollatzResearch.WordTrace tailWord_8301603 prefixEnd_8301603 4262712541806788673784129 := by
  unfold tailWord_8301603
  simp only [CollatzResearch.WordTrace]
  refine ⟨302784336143717606760613463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201856224095811737840408975 302784336143717606760613463)
  ·
    refine ⟨454176504215576410140920195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302784336143717606760613463 454176504215576410140920195)
    ·
      refine ⟨681264756323364615211380293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454176504215576410140920195 681264756323364615211380293)
      ·
        refine ⟨127737141810630865352133805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 681264756323364615211380293 127737141810630865352133805)
        ·
          refine ⟨47901428178986574507050177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127737141810630865352133805 47901428178986574507050177)
          ·
            refine ⟨35926071134239930880287633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47901428178986574507050177 35926071134239930880287633)
            ·
              refine ⟨26944553350679948160215725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35926071134239930880287633 26944553350679948160215725)
              ·
                refine ⟨10104207506504980560080897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26944553350679948160215725 10104207506504980560080897)
                ·
                  refine ⟨7578155629878735420060673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10104207506504980560080897 7578155629878735420060673)
                  ·
                    refine ⟨5683616722409051565045505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578155629878735420060673 5683616722409051565045505)
                    ·
                      refine ⟨4262712541806788673784129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683616722409051565045505 4262712541806788673784129)
                      ·
                        rfl

theorem cell23_8301603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_8301603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301603 prefixEnd_8301603 := by exact prefixLift 8301603
  have htrace : WordTrace (prefixWord ++ tailWord_8301603) baseStart_8301603 baseEnd_8301603 := by
    simpa [prefixWord, tailWord_8301603, baseEnd_8301603] using wordTrace_append hprefix tailTrace_8301603
  have hstable : (prefixWord ++ tailWord_8301603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301603).length < 2 ^ (prefixWord ++ tailWord_8301603).sum := by decide
  have hdescent : baseEnd_8301603 < baseStart_8301603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301654 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_8301654 : Nat := 118140960795 + 8301654 * 2 ^ 59
def prefixEnd_8301654 : Nat := 4983230072969 + 3 ^ 40 * 8301654 * 2
def baseEnd_8301654 : Nat := 4262738729320167974246395

theorem tailTrace_8301654 : CollatzResearch.WordTrace tailWord_8301654 prefixEnd_8301654 4262738729320167974246395 := by
  unfold tailWord_8301654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924137266658302654420001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201857464177688561647146677 18924137266658302654420001)
  ·
    refine ⟨14193102949993726990815001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18924137266658302654420001 14193102949993726990815001)
    ·
      refine ⟨10644827212495295243111251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14193102949993726990815001 10644827212495295243111251)
      ·
        refine ⟨15967240818742942864666877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644827212495295243111251 15967240818742942864666877)
        ·
          refine ⟨5987715307028603574250079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15967240818742942864666877 5987715307028603574250079)
          ·
            refine ⟨8981572960542905361375119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987715307028603574250079 8981572960542905361375119)
            ·
              refine ⟨13472359440814358042062679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981572960542905361375119 13472359440814358042062679)
              ·
                refine ⟨20208539161221537063094019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13472359440814358042062679 20208539161221537063094019)
                ·
                  refine ⟨30312808741832305594641029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20208539161221537063094019 30312808741832305594641029)
                  ·
                    refine ⟨5683651639093557298995193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30312808741832305594641029 5683651639093557298995193)
                    ·
                      refine ⟨4262738729320167974246395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683651639093557298995193 4262738729320167974246395)
                      ·
                        rfl

theorem cell23_8301654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_8301654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301654 prefixEnd_8301654 := by exact prefixLift 8301654
  have htrace : WordTrace (prefixWord ++ tailWord_8301654) baseStart_8301654 baseEnd_8301654 := by
    simpa [prefixWord, tailWord_8301654, baseEnd_8301654] using wordTrace_append hprefix tailTrace_8301654
  have hstable : (prefixWord ++ tailWord_8301654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301654).length < 2 ^ (prefixWord ++ tailWord_8301654).sum := by decide
  have hdescent : baseEnd_8301654 < baseStart_8301654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301679 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_8301679 : Nat := 118140960795 + 8301679 * 2 ^ 59
def prefixEnd_8301679 : Nat := 4983230072969 + 3 ^ 40 * 8301679 * 2
def baseEnd_8301679 : Nat := 4262751566336530376433779

theorem tailTrace_8301679 : CollatzResearch.WordTrace tailWord_8301679 prefixEnd_8301679 4262751566336530376433779 := by
  unfold tailWord_8301679
  simp only [CollatzResearch.WordTrace]
  refine ⟨302787108091442271740380091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201858072060961514493586727 302787108091442271740380091)
  ·
    refine ⟨454180662137163407610570137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302787108091442271740380091 454180662137163407610570137)
    ·
      refine ⟨340635496602872555707927603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454180662137163407610570137 340635496602872555707927603)
      ·
        refine ⟨510953244904308833561891405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340635496602872555707927603 510953244904308833561891405)
        ·
          refine ⟨191607466839115812585709277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510953244904308833561891405 191607466839115812585709277)
          ·
            refine ⟨71852800064668429719640979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191607466839115812585709277 71852800064668429719640979)
            ·
              refine ⟨107779200097002644579461469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71852800064668429719640979 107779200097002644579461469)
              ·
                refine ⟨40417200036375991717298051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107779200097002644579461469 40417200036375991717298051)
                ·
                  refine ⟨60625800054563987575947077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40417200036375991717298051 60625800054563987575947077)
                  ·
                    refine ⟨11367337510230747670490077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60625800054563987575947077 11367337510230747670490077)
                    ·
                      refine ⟨4262751566336530376433779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367337510230747670490077 4262751566336530376433779)
                      ·
                        rfl

theorem cell23_8301679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_8301679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301679 prefixEnd_8301679 := by exact prefixLift 8301679
  have htrace : WordTrace (prefixWord ++ tailWord_8301679) baseStart_8301679 baseEnd_8301679 := by
    simpa [prefixWord, tailWord_8301679, baseEnd_8301679] using wordTrace_append hprefix tailTrace_8301679
  have hstable : (prefixWord ++ tailWord_8301679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301679).length < 2 ^ (prefixWord ++ tailWord_8301679).sum := by decide
  have hdescent : baseEnd_8301679 < baseStart_8301679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301694 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_8301694 : Nat := 118140960795 + 8301694 * 2 ^ 59
def prefixEnd_8301694 : Nat := 4983230072969 + 3 ^ 40 * 8301694 * 2
def baseEnd_8301694 : Nat := 473639918727371979749579

theorem tailTrace_8301694 : CollatzResearch.WordTrace tailWord_8301694 prefixEnd_8301694 473639918727371979749579 := by
  unfold tailWord_8301694
  simp only [CollatzResearch.WordTrace]
  refine ⟨37848456898298491162772017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201858436790925286201450757 37848456898298491162772017)
  ·
    refine ⟨28386342673723868372079013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37848456898298491162772017 28386342673723868372079013)
    ·
      refine ⟨5322439251323225319764815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28386342673723868372079013 5322439251323225319764815)
      ·
        refine ⟨7983658876984837979647223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322439251323225319764815 7983658876984837979647223)
        ·
          refine ⟨11975488315477256969470835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983658876984837979647223 11975488315477256969470835)
          ·
            refine ⟨17963232473215885454206253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11975488315477256969470835 17963232473215885454206253)
            ·
              refine ⟨6736212177455957045327345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17963232473215885454206253 6736212177455957045327345)
              ·
                refine ⟨5052159133091967783995509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736212177455957045327345 5052159133091967783995509)
                ·
                  refine ⟨473639918727371979749579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5052159133091967783995509 473639918727371979749579)
                  ·
                    rfl

theorem cell23_8301694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_8301694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301694 prefixEnd_8301694 := by exact prefixLift 8301694
  have htrace : WordTrace (prefixWord ++ tailWord_8301694) baseStart_8301694 baseEnd_8301694 := by
    simpa [prefixWord, tailWord_8301694, baseEnd_8301694] using wordTrace_append hprefix tailTrace_8301694
  have hstable : (prefixWord ++ tailWord_8301694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301694).length < 2 ^ (prefixWord ++ tailWord_8301694).sum := by decide
  have hdescent : baseEnd_8301694 < baseStart_8301694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301699 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 6]
def baseStart_8301699 : Nat := 118140960795 + 8301699 * 2 ^ 59
def prefixEnd_8301699 : Nat := 4983230072969 + 3 ^ 40 * 8301699 * 2
def baseEnd_8301699 : Nat := 473640203994402255353743

theorem tailTrace_8301699 : CollatzResearch.WordTrace tailWord_8301699 prefixEnd_8301699 473640203994402255353743 := by
  unfold tailWord_8301699
  simp only [CollatzResearch.WordTrace]
  refine ⟨302787837551369815156108151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201858558367579876770738767 302787837551369815156108151)
  ·
    refine ⟨454181756327054722734162227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302787837551369815156108151 454181756327054722734162227)
    ·
      refine ⟨681272634490582084101243341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454181756327054722734162227 681272634490582084101243341)
      ·
        refine ⟨255477237933968281537966253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681272634490582084101243341 255477237933968281537966253)
        ·
          refine ⟨95803964225238105576737345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255477237933968281537966253 95803964225238105576737345)
          ·
            refine ⟨71852973168928579182553009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95803964225238105576737345 71852973168928579182553009)
            ·
              refine ⟨53889729876696434386914757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71852973168928579182553009 53889729876696434386914757)
              ·
                refine ⟨10104324351880581447546517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53889729876696434386914757 10104324351880581447546517)
                ·
                  refine ⟨473640203994402255353743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10104324351880581447546517 473640203994402255353743)
                  ·
                    rfl

theorem cell23_8301699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 6].length) (baseStart_8301699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301699 prefixEnd_8301699 := by exact prefixLift 8301699
  have htrace : WordTrace (prefixWord ++ tailWord_8301699) baseStart_8301699 baseEnd_8301699 := by
    simpa [prefixWord, tailWord_8301699, baseEnd_8301699] using wordTrace_append hprefix tailTrace_8301699
  have hstable : (prefixWord ++ tailWord_8301699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301699).length < 2 ^ (prefixWord ++ tailWord_8301699).sum := by decide
  have hdescent : baseEnd_8301699 < baseStart_8301699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301730 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_8301730 : Nat := 118140960795 + 8301730 * 2 ^ 59
def prefixEnd_8301730 : Nat := 4983230072969 + 3 ^ 40 * 8301730 * 2
def baseEnd_8301730 : Nat := 4262777753849909676896045

theorem tailTrace_8301730 : CollatzResearch.WordTrace tailWord_8301730 prefixEnd_8301730 4262777753849909676896045 := by
  unfold tailWord_8301730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75697242053564376862621661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201859312142838338300324429 75697242053564376862621661)
  ·
    refine ⟨28386465770086641323483123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75697242053564376862621661 28386465770086641323483123)
    ·
      refine ⟨42579698655129961985224685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28386465770086641323483123 42579698655129961985224685)
      ·
        refine ⟨15967386995673735744459257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42579698655129961985224685 15967386995673735744459257)
        ·
          refine ⟨11975540246755301808344443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15967386995673735744459257 11975540246755301808344443)
          ·
            refine ⟨17963310370132952712516665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11975540246755301808344443 17963310370132952712516665)
            ·
              refine ⟨13472482777599714534387499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17963310370132952712516665 13472482777599714534387499)
              ·
                refine ⟨20208724166399571801581249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13472482777599714534387499 20208724166399571801581249)
                ·
                  refine ⟨15156543124799678851185937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20208724166399571801581249 15156543124799678851185937)
                  ·
                    refine ⟨11367407343599759138389453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15156543124799678851185937 11367407343599759138389453)
                    ·
                      refine ⟨4262777753849909676896045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367407343599759138389453 4262777753849909676896045)
                      ·
                        rfl

theorem cell23_8301730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_8301730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301730 prefixEnd_8301730 := by exact prefixLift 8301730
  have htrace : WordTrace (prefixWord ++ tailWord_8301730) baseStart_8301730 baseEnd_8301730 := by
    simpa [prefixWord, tailWord_8301730, baseEnd_8301730] using wordTrace_append hprefix tailTrace_8301730
  have hstable : (prefixWord ++ tailWord_8301730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301730).length < 2 ^ (prefixWord ++ tailWord_8301730).sum := by decide
  have hdescent : baseEnd_8301730 < baseStart_8301730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301753 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 2, 3, 2]
def baseStart_8301753 : Nat := 118140960795 + 8301753 * 2 ^ 59
def prefixEnd_8301753 : Nat := 4983230072969 + 3 ^ 40 * 8301753 * 2
def baseEnd_8301753 : Nat := 4262789563904963086908439

theorem tailTrace_8301753 : CollatzResearch.WordTrace tailWord_8301753 prefixEnd_8301753 4262789563904963086908439 := by
  unfold tailWord_8301753
  simp only [CollatzResearch.WordTrace]
  refine ⟨302789807093174182378573913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201859871395449454919049275 302789807093174182378573913)
  ·
    refine ⟨227092355319880636783930435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302789807093174182378573913 227092355319880636783930435)
    ·
      refine ⟨340638532979820955175895653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227092355319880636783930435 340638532979820955175895653)
      ·
        refine ⟨63869724933716429095480435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340638532979820955175895653 63869724933716429095480435)
        ·
          refine ⟨95804587400574643643220653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63869724933716429095480435 95804587400574643643220653)
          ·
            refine ⟨35926720275215491366207745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95804587400574643643220653 35926720275215491366207745)
            ·
              refine ⟨26945040206411618524655809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35926720275215491366207745 26945040206411618524655809)
              ·
                refine ⟨20208780154808713893491857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26945040206411618524655809 20208780154808713893491857)
                ·
                  refine ⟨15156585116106535420118893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20208780154808713893491857 15156585116106535420118893)
                  ·
                    refine ⟨5683719418539950782544585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15156585116106535420118893 5683719418539950782544585)
                    ·
                      refine ⟨4262789563904963086908439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683719418539950782544585 4262789563904963086908439)
                      ·
                        rfl

theorem cell23_8301753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_8301753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301753 prefixEnd_8301753 := by exact prefixLift 8301753
  have htrace : WordTrace (prefixWord ++ tailWord_8301753) baseStart_8301753 baseEnd_8301753 := by
    simpa [prefixWord, tailWord_8301753, baseEnd_8301753] using wordTrace_append hprefix tailTrace_8301753
  have hstable : (prefixWord ++ tailWord_8301753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301753).length < 2 ^ (prefixWord ++ tailWord_8301753).sum := by decide
  have hdescent : baseEnd_8301753 < baseStart_8301753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301779 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_8301779 : Nat := 118140960795 + 8301779 * 2 ^ 59
def prefixEnd_8301779 : Nat := 4983230072969 + 3 ^ 40 * 8301779 * 2
def baseEnd_8301779 : Nat := 4262802914401979985183319

theorem tailTrace_8301779 : CollatzResearch.WordTrace tailWord_8301779 prefixEnd_8301779 4262802914401979985183319 := by
  unfold tailWord_8301779
  simp only [CollatzResearch.WordTrace]
  refine ⟨302790755391079988819020391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201860503594053325879346927 302790755391079988819020391)
  ·
    refine ⟨454186133086619983228530587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302790755391079988819020391 454186133086619983228530587)
    ·
      refine ⟨681279199629929974842795881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454186133086619983228530587 681279199629929974842795881)
      ·
        refine ⟨510959399722447481132096911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681279199629929974842795881 510959399722447481132096911)
        ·
          refine ⟨766439099583671221698145367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510959399722447481132096911 766439099583671221698145367)
          ·
            refine ⟨1149658649375506832547218051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766439099583671221698145367 1149658649375506832547218051)
            ·
              refine ⟨1724487974063260248820827077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149658649375506832547218051 1724487974063260248820827077)
              ·
                refine ⟨323341495136861296653905077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1724487974063260248820827077 323341495136861296653905077)
                ·
                  refine ⟨30313265169080746561303601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323341495136861296653905077 30313265169080746561303601)
                  ·
                    refine ⟨22734948876810559920977701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30313265169080746561303601 22734948876810559920977701)
                    ·
                      refine ⟨4262802914401979985183319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22734948876810559920977701 4262802914401979985183319)
                      ·
                        rfl

theorem cell23_8301779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_8301779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301779 prefixEnd_8301779 := by exact prefixLift 8301779
  have htrace : WordTrace (prefixWord ++ tailWord_8301779) baseStart_8301779 baseEnd_8301779 := by
    simpa [prefixWord, tailWord_8301779, baseEnd_8301779] using wordTrace_append hprefix tailTrace_8301779
  have hstable : (prefixWord ++ tailWord_8301779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301779).length < 2 ^ (prefixWord ++ tailWord_8301779).sum := by decide
  have hdescent : baseEnd_8301779 < baseStart_8301779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301783 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_8301783 : Nat := 118140960795 + 8301783 * 2 ^ 59
def prefixEnd_8301783 : Nat := 4983230072969 + 3 ^ 40 * 8301783 * 2
def baseEnd_8301783 : Nat := 4262804968324597969533301

theorem tailTrace_8301783 : CollatzResearch.WordTrace tailWord_8301783 prefixEnd_8301783 4262804968324597969533301 := by
  unfold tailWord_8301783
  simp only [CollatzResearch.WordTrace]
  refine ⟨302790901283065497502166003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201860600855376998334777335 302790901283065497502166003)
  ·
    refine ⟨454186351924598246253249005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302790901283065497502166003 454186351924598246253249005)
    ·
      refine ⟨170319881971724342344968377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454186351924598246253249005 170319881971724342344968377)
      ·
        refine ⟨127739911478793256758726283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170319881971724342344968377 127739911478793256758726283)
        ·
          refine ⟨191609867218189885138089425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127739911478793256758726283 191609867218189885138089425)
          ·
            refine ⟨143707400413642413853567069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191609867218189885138089425 143707400413642413853567069)
            ·
              refine ⟨53890275155115905195087651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143707400413642413853567069 53890275155115905195087651)
              ·
                refine ⟨80835412732673857792631477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53890275155115905195087651 80835412732673857792631477)
                ·
                  refine ⟨7578319943688174168059201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80835412732673857792631477 7578319943688174168059201)
                  ·
                    refine ⟨5683739957766130626044401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578319943688174168059201 5683739957766130626044401)
                    ·
                      refine ⟨4262804968324597969533301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683739957766130626044401 4262804968324597969533301)
                      ·
                        rfl

theorem cell23_8301783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_8301783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301783 prefixEnd_8301783 := by exact prefixLift 8301783
  have htrace : WordTrace (prefixWord ++ tailWord_8301783) baseStart_8301783 baseEnd_8301783 := by
    simpa [prefixWord, tailWord_8301783, baseEnd_8301783] using wordTrace_append hprefix tailTrace_8301783
  have hstable : (prefixWord ++ tailWord_8301783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301783).length < 2 ^ (prefixWord ++ tailWord_8301783).sum := by decide
  have hdescent : baseEnd_8301783 < baseStart_8301783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301796 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_8301796 : Nat := 118140960795 + 8301796 * 2 ^ 59
def prefixEnd_8301796 : Nat := 4983230072969 + 3 ^ 40 * 8301796 * 2
def baseEnd_8301796 : Nat := 4262811643573106418670741

theorem tailTrace_8301796 : CollatzResearch.WordTrace tailWord_8301796 prefixEnd_8301796 4262811643573106418670741 := by
  unfold tailWord_8301796
  simp only [CollatzResearch.WordTrace]
  refine ⟨151395687716009200361194621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201860916954678933814926161 151395687716009200361194621)
  ·
    refine ⟨56773382893503450135447983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151395687716009200361194621 56773382893503450135447983)
    ·
      refine ⟨85160074340255175203171975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56773382893503450135447983 85160074340255175203171975)
      ·
        refine ⟨127740111510382762804757963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85160074340255175203171975 127740111510382762804757963)
        ·
          refine ⟨191610167265574144207136945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127740111510382762804757963 191610167265574144207136945)
          ·
            refine ⟨143707625449180608155352709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191610167265574144207136945 143707625449180608155352709)
            ·
              refine ⟨26945179771721364029128633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143707625449180608155352709 26945179771721364029128633)
              ·
                refine ⟨20208884828791023021846475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26945179771721364029128633 20208884828791023021846475)
                ·
                  refine ⟨30313327243186534532769713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20208884828791023021846475 30313327243186534532769713)
                  ·
                    refine ⟨22734995432389900899577285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30313327243186534532769713 22734995432389900899577285)
                    ·
                      refine ⟨4262811643573106418670741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22734995432389900899577285 4262811643573106418670741)
                      ·
                        rfl

theorem cell23_8301796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_8301796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301796 prefixEnd_8301796 := by exact prefixLift 8301796
  have htrace : WordTrace (prefixWord ++ tailWord_8301796) baseStart_8301796 baseEnd_8301796 := by
    simpa [prefixWord, tailWord_8301796, baseEnd_8301796] using wordTrace_append hprefix tailTrace_8301796
  have hstable : (prefixWord ++ tailWord_8301796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301796).length < 2 ^ (prefixWord ++ tailWord_8301796).sum := by decide
  have hdescent : baseEnd_8301796 < baseStart_8301796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301797 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_8301797 : Nat := 118140960795 + 8301797 * 2 ^ 59
def prefixEnd_8301797 : Nat := 4983230072969 + 3 ^ 40 * 8301797 * 2
def baseEnd_8301797 : Nat := 1420937385684586971586079

theorem tailTrace_8301797 : CollatzResearch.WordTrace tailWord_8301797 prefixEnd_8301797 1420937385684586971586079 := by
  unfold tailWord_8301797
  simp only [CollatzResearch.WordTrace]
  refine ⟨302791411905014777893175645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201860941270009851928783763 302791411905014777893175645)
  ·
    refine ⟨113546779464380541709940867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302791411905014777893175645 113546779464380541709940867)
    ·
      refine ⟨170320169196570812564911301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113546779464380541709940867 170320169196570812564911301)
      ·
        refine ⟨31935031724357027355920869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170320169196570812564911301 31935031724357027355920869)
        ·
          refine ⟨5987818448316942629235163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31935031724357027355920869 5987818448316942629235163)
          ·
            refine ⟨8981727672475413943852745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987818448316942629235163 8981727672475413943852745)
            ·
              refine ⟨6736295754356560457889559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981727672475413943852745 6736295754356560457889559)
              ·
                refine ⟨10104443631534840686834339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736295754356560457889559 10104443631534840686834339)
                ·
                  refine ⟨15156665447302261030251509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104443631534840686834339 15156665447302261030251509)
                  ·
                    refine ⟨1420937385684586971586079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15156665447302261030251509 1420937385684586971586079)
                    ·
                      rfl

theorem cell23_8301797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_8301797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301797 prefixEnd_8301797 := by exact prefixLift 8301797
  have htrace : WordTrace (prefixWord ++ tailWord_8301797) baseStart_8301797 baseEnd_8301797 := by
    simpa [prefixWord, tailWord_8301797, baseEnd_8301797] using wordTrace_append hprefix tailTrace_8301797
  have hstable : (prefixWord ++ tailWord_8301797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301797).length < 2 ^ (prefixWord ++ tailWord_8301797).sum := by decide
  have hdescent : baseEnd_8301797 < baseStart_8301797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301803 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 3]
def baseStart_8301803 : Nat := 118140960795 + 8301803 * 2 ^ 59
def prefixEnd_8301803 : Nat := 4983230072969 + 3 ^ 40 * 8301803 * 2
def baseEnd_8301803 : Nat := 4262815237937687891283209

theorem tailTrace_8301803 : CollatzResearch.WordTrace tailWord_8301803 prefixEnd_8301803 4262815237937687891283209 := by
  unfold tailWord_8301803
  simp only [CollatzResearch.WordTrace]
  refine ⟨302791630742993040917894063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201861087161995360611929375 302791630742993040917894063)
  ·
    refine ⟨454187446114489561376841095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302791630742993040917894063 454187446114489561376841095)
    ·
      refine ⟨681281169171734342065261643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454187446114489561376841095 681281169171734342065261643)
      ·
        refine ⟨1021921753757601513097892465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681281169171734342065261643 1021921753757601513097892465)
        ·
          refine ⟨766441315318201134823419349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021921753757601513097892465 766441315318201134823419349)
          ·
            refine ⟨17963468327770339097423891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 766441315318201134823419349 17963468327770339097423891)
            ·
              refine ⟨26945202491655508646135837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17963468327770339097423891 26945202491655508646135837)
              ·
                refine ⟨10104450934370815742300939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26945202491655508646135837 10104450934370815742300939)
                ·
                  refine ⟨15156676401556223613451409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104450934370815742300939 15156676401556223613451409)
                  ·
                    refine ⟨11367507301167167710088557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15156676401556223613451409 11367507301167167710088557)
                    ·
                      refine ⟨4262815237937687891283209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367507301167167710088557 4262815237937687891283209)
                      ·
                        rfl

theorem cell23_8301803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 2, 3].length) (baseStart_8301803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301803 prefixEnd_8301803 := by exact prefixLift 8301803
  have htrace : WordTrace (prefixWord ++ tailWord_8301803) baseStart_8301803 baseEnd_8301803 := by
    simpa [prefixWord, tailWord_8301803, baseEnd_8301803] using wordTrace_append hprefix tailTrace_8301803
  have hstable : (prefixWord ++ tailWord_8301803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301803).length < 2 ^ (prefixWord ++ tailWord_8301803).sum := by decide
  have hdescent : baseEnd_8301803 < baseStart_8301803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301809 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_8301809 : Nat := 118140960795 + 8301809 * 2 ^ 59
def prefixEnd_8301809 : Nat := 4983230072969 + 3 ^ 40 * 8301809 * 2
def baseEnd_8301809 : Nat := 4262818318821614867808181

theorem tailTrace_8301809 : CollatzResearch.WordTrace tailWord_8301809 prefixEnd_8301809 4262818318821614867808181 := by
  unfold tailWord_8301809
  simp only [CollatzResearch.WordTrace]
  refine ⟨302791849580971303942612481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201861233053980869295074987 302791849580971303942612481)
  ·
    refine ⟨227093887185728477956959361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302791849580971303942612481 227093887185728477956959361)
    ·
      refine ⟨170320415389296358467719521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227093887185728477956959361 170320415389296358467719521)
      ·
        refine ⟨127740311541972268850789641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170320415389296358467719521 127740311541972268850789641)
        ·
          refine ⟨95805233656479201638092231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127740311541972268850789641 95805233656479201638092231)
          ·
            refine ⟨143707850484718802457138347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95805233656479201638092231 143707850484718802457138347)
            ·
              refine ⟨215561775727078203685707521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143707850484718802457138347 215561775727078203685707521)
              ·
                refine ⟨161671331795308652764280641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215561775727078203685707521 161671331795308652764280641)
                ·
                  refine ⟨121253498846481489573210481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161671331795308652764280641 121253498846481489573210481)
                  ·
                    refine ⟨90940124134861117179907861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121253498846481489573210481 90940124134861117179907861)
                    ·
                      refine ⟨4262818318821614867808181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90940124134861117179907861 4262818318821614867808181)
                      ·
                        rfl

theorem cell23_8301809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_8301809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301809 prefixEnd_8301809 := by exact prefixLift 8301809
  have htrace : WordTrace (prefixWord ++ tailWord_8301809) baseStart_8301809 baseEnd_8301809 := by
    simpa [prefixWord, tailWord_8301809, baseEnd_8301809] using wordTrace_append hprefix tailTrace_8301809
  have hstable : (prefixWord ++ tailWord_8301809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301809).length < 2 ^ (prefixWord ++ tailWord_8301809).sum := by decide
  have hdescent : baseEnd_8301809 < baseStart_8301809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301860 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_8301860 : Nat := 118140960795 + 8301860 * 2 ^ 59
def prefixEnd_8301860 : Nat := 4983230072969 + 3 ^ 40 * 8301860 * 2
def baseEnd_8301860 : Nat := 4262844506334994168270447

theorem tailTrace_8301860 : CollatzResearch.WordTrace tailWord_8301860 prefixEnd_8301860 4262844506334994168270447 := by
  unfold tailWord_8301860
  simp only [CollatzResearch.WordTrace]
  refine ⟨151396854851893269826359517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201862473135857693101812689 151396854851893269826359517)
  ·
    refine ⟨56773820569459976184884819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151396854851893269826359517 56773820569459976184884819)
    ·
      refine ⟨85160730854189964277327229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56773820569459976184884819 85160730854189964277327229)
      ·
        refine ⟨31935274070321236603997711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85160730854189964277327229 31935274070321236603997711)
        ·
          refine ⟨47902911105481854905996567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31935274070321236603997711 47902911105481854905996567)
          ·
            refine ⟨71854366658222782358994851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47902911105481854905996567 71854366658222782358994851)
            ·
              refine ⟨107781549987334173538492277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71854366658222782358994851 107781549987334173538492277)
              ·
                refine ⟨10104520311312578769233651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107781549987334173538492277 10104520311312578769233651)
                ·
                  refine ⟨15156780466968868153850477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104520311312578769233651 15156780466968868153850477)
                  ·
                    refine ⟨5683792675113325557693929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15156780466968868153850477 5683792675113325557693929)
                    ·
                      refine ⟨4262844506334994168270447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683792675113325557693929 4262844506334994168270447)
                      ·
                        rfl

theorem cell23_8301860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_8301860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301860 prefixEnd_8301860 := by exact prefixLift 8301860
  have htrace : WordTrace (prefixWord ++ tailWord_8301860) baseStart_8301860 baseEnd_8301860 := by
    simpa [prefixWord, tailWord_8301860, baseEnd_8301860] using wordTrace_append hprefix tailTrace_8301860
  have hstable : (prefixWord ++ tailWord_8301860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301860).length < 2 ^ (prefixWord ++ tailWord_8301860).sum := by decide
  have hdescent : baseEnd_8301860 < baseStart_8301860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301936 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_8301936 : Nat := 118140960795 + 8301936 * 2 ^ 59
def prefixEnd_8301936 : Nat := 4983230072969 + 3 ^ 40 * 8301936 * 2
def baseEnd_8301936 : Nat := 4262883530864735870920097

theorem tailTrace_8301936 : CollatzResearch.WordTrace tailWord_8301936 prefixEnd_8301936 4262883530864735870920097 := by
  unfold tailWord_8301936
  simp only [CollatzResearch.WordTrace]
  refine ⟨151398240825755602316242831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201864321101007469754990441 151398240825755602316242831)
  ·
    refine ⟨227097361238633403474364247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151398240825755602316242831 227097361238633403474364247)
    ·
      refine ⟨340646041857950105211546371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227097361238633403474364247 340646041857950105211546371)
      ·
        refine ⟨510969062786925157817319557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340646041857950105211546371 510969062786925157817319557)
        ·
          refine ⟨95806699272548467090747417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510969062786925157817319557 95806699272548467090747417)
          ·
            refine ⟨71855024454411350318060563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95806699272548467090747417 71855024454411350318060563)
            ·
              refine ⟨107782536681617025477090845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71855024454411350318060563 107782536681617025477090845)
              ·
                refine ⟨40418451255606384553909067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107782536681617025477090845 40418451255606384553909067)
                ·
                  refine ⟨60627676883409576830863601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40418451255606384553909067 60627676883409576830863601)
                  ·
                    refine ⟨45470757662557182623147701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60627676883409576830863601 45470757662557182623147701)
                    ·
                      refine ⟨4262883530864735870920097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45470757662557182623147701 4262883530864735870920097)
                      ·
                        rfl

theorem cell23_8301936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_8301936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301936 prefixEnd_8301936 := by exact prefixLift 8301936
  have htrace : WordTrace (prefixWord ++ tailWord_8301936) baseStart_8301936 baseEnd_8301936 := by
    simpa [prefixWord, tailWord_8301936, baseEnd_8301936] using wordTrace_append hprefix tailTrace_8301936
  have hstable : (prefixWord ++ tailWord_8301936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301936).length < 2 ^ (prefixWord ++ tailWord_8301936).sum := by decide
  have hdescent : baseEnd_8301936 < baseStart_8301936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301946 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_8301946 : Nat := 118140960795 + 8301946 * 2 ^ 59
def prefixEnd_8301946 : Nat := 4983230072969 + 3 ^ 40 * 8301946 * 2
def baseEnd_8301946 : Nat := 4262888665671280831795051

theorem tailTrace_8301946 : CollatzResearch.WordTrace tailWord_8301946 prefixEnd_8301946 4262888665671280831795051 := by
  unfold tailWord_8301946
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699211595368744085087423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201864564254316650893566461 75699211595368744085087423)
  ·
    refine ⟨113548817393053116127631135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75699211595368744085087423 113548817393053116127631135)
    ·
      refine ⟨170323226089579674191446703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113548817393053116127631135 170323226089579674191446703)
      ·
        refine ⟨255484839134369511287170055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170323226089579674191446703 255484839134369511287170055)
        ·
          refine ⟨383227258701554266930755083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255484839134369511287170055 383227258701554266930755083)
          ·
            refine ⟨574840888052331400396132625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383227258701554266930755083 574840888052331400396132625)
            ·
              refine ⟨431130666039248550297099469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574840888052331400396132625 431130666039248550297099469)
              ·
                refine ⟨161673999764718206361412301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431130666039248550297099469 161673999764718206361412301)
                ·
                  refine ⟨60627749911769327385529613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161673999764718206361412301 60627749911769327385529613)
                  ·
                    refine ⟨22735406216913497769573605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60627749911769327385529613 22735406216913497769573605)
                    ·
                      refine ⟨4262888665671280831795051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22735406216913497769573605 4262888665671280831795051)
                      ·
                        rfl

theorem cell23_8301946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_8301946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301946 prefixEnd_8301946 := by exact prefixLift 8301946
  have htrace : WordTrace (prefixWord ++ tailWord_8301946) baseStart_8301946 baseEnd_8301946 := by
    simpa [prefixWord, tailWord_8301946, baseEnd_8301946] using wordTrace_append hprefix tailTrace_8301946
  have hstable : (prefixWord ++ tailWord_8301946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301946).length < 2 ^ (prefixWord ++ tailWord_8301946).sum := by decide
  have hdescent : baseEnd_8301946 < baseStart_8301946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301960 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_8301960 : Nat := 118140960795 + 8301960 * 2 ^ 59
def prefixEnd_8301960 : Nat := 4983230072969 + 3 ^ 40 * 8301960 * 2
def baseEnd_8301960 : Nat := 1420965284800147925673329

theorem tailTrace_8301960 : CollatzResearch.WordTrace tailWord_8301960 prefixEnd_8301960 1420965284800147925673329 := by
  unfold tailWord_8301960
  simp only [CollatzResearch.WordTrace]
  refine ⟨151398678501712128365679667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201864904668949504487572889 151398678501712128365679667)
  ·
    refine ⟨227098017752568192548519501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151398678501712128365679667 227098017752568192548519501)
    ·
      refine ⟨85161756657213072205694813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227098017752568192548519501 85161756657213072205694813)
      ·
        refine ⟨31935658746454902077135555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85161756657213072205694813 31935658746454902077135555)
        ·
          refine ⟨47903488119682353115703333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31935658746454902077135555 47903488119682353115703333)
          ·
            refine ⟨8981904022440441209194375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47903488119682353115703333 8981904022440441209194375)
            ·
              refine ⟨13472856033660661813791563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981904022440441209194375 13472856033660661813791563)
              ·
                refine ⟨20209284050490992720687345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13472856033660661813791563 20209284050490992720687345)
                ·
                  refine ⟨15156963037868244540515509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20209284050490992720687345 15156963037868244540515509)
                  ·
                    refine ⟨1420965284800147925673329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15156963037868244540515509 1420965284800147925673329)
                    ·
                      rfl

theorem cell23_8301960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_8301960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301960 prefixEnd_8301960 := by exact prefixLift 8301960
  have htrace : WordTrace (prefixWord ++ tailWord_8301960) baseStart_8301960 baseEnd_8301960 := by
    simpa [prefixWord, tailWord_8301960, baseEnd_8301960] using wordTrace_append hprefix tailTrace_8301960
  have hstable : (prefixWord ++ tailWord_8301960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301960).length < 2 ^ (prefixWord ++ tailWord_8301960).sum := by decide
  have hdescent : baseEnd_8301960 < baseStart_8301960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301963 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 6, 2]
def baseStart_8301963 : Nat := 118140960795 + 8301963 * 2 ^ 59
def prefixEnd_8301963 : Nat := 4983230072969 + 3 ^ 40 * 8301963 * 2
def baseEnd_8301963 : Nat := 4262897394842407265282473

theorem tailTrace_8301963 : CollatzResearch.WordTrace tailWord_8301963 prefixEnd_8301963 4262897394842407265282473 := by
  unfold tailWord_8301963
  simp only [CollatzResearch.WordTrace]
  refine ⟨302797466422413388243718543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201864977614942258829145695 302797466422413388243718543)
  ·
    refine ⟨454196199633620082365577815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302797466422413388243718543 454196199633620082365577815)
    ·
      refine ⟨681294299450430123548366723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454196199633620082365577815 681294299450430123548366723)
      ·
        refine ⟨1021941449175645185322550085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681294299450430123548366723 1021941449175645185322550085)
        ·
          refine ⟨191614021720433472247978141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1021941449175645185322550085 191614021720433472247978141)
          ·
            refine ⟨71855258145162552092991803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191614021720433472247978141 71855258145162552092991803)
            ·
              refine ⟨107782887217743828139487705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71855258145162552092991803 107782887217743828139487705)
              ·
                refine ⟨80837165413307871104615779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107782887217743828139487705 80837165413307871104615779)
                ·
                  refine ⟨121255748119961806656923669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80837165413307871104615779 121255748119961806656923669)
                  ·
                    refine ⟨5683863193123209687043297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121255748119961806656923669 5683863193123209687043297)
                    ·
                      refine ⟨4262897394842407265282473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683863193123209687043297 4262897394842407265282473)
                      ·
                        rfl

theorem cell23_8301963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 6, 2].length) (baseStart_8301963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301963 prefixEnd_8301963 := by exact prefixLift 8301963
  have htrace : WordTrace (prefixWord ++ tailWord_8301963) baseStart_8301963 baseEnd_8301963 := by
    simpa [prefixWord, tailWord_8301963, baseEnd_8301963] using wordTrace_append hprefix tailTrace_8301963
  have hstable : (prefixWord ++ tailWord_8301963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301963).length < 2 ^ (prefixWord ++ tailWord_8301963).sum := by decide
  have hdescent : baseEnd_8301963 < baseStart_8301963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8301997 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_8301997 : Nat := 118140960795 + 8301997 * 2 ^ 59
def prefixEnd_8301997 : Nat := 4983230072969 + 3 ^ 40 * 8301997 * 2
def baseEnd_8301997 : Nat := 4262914853184660132257317

theorem tailTrace_8301997 : CollatzResearch.WordTrace tailWord_8301997 prefixEnd_8301997 4262914853184660132257317 := by
  unfold tailWord_8301997
  simp only [CollatzResearch.WordTrace]
  refine ⟨302798706504290212050456245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201865804336193474700304163 302798706504290212050456245)
  ·
    refine ⟨28387378734777207379730273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302798706504290212050456245 28387378734777207379730273)
    ·
      refine ⟨21290534051082905534797705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28387378734777207379730273 21290534051082905534797705)
      ·
        refine ⟨15967900538312179151098279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21290534051082905534797705 15967900538312179151098279)
        ·
          refine ⟨23951850807468268726647419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15967900538312179151098279 23951850807468268726647419)
          ·
            refine ⟨35927776211202403089971129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23951850807468268726647419 35927776211202403089971129)
            ·
              refine ⟨26945832158401802317478347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35927776211202403089971129 26945832158401802317478347)
              ·
                refine ⟨40418748237602703476217521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26945832158401802317478347 40418748237602703476217521)
                ·
                  refine ⟨30314061178202027607163141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40418748237602703476217521 30314061178202027607163141)
                  ·
                    refine ⟨5683886470912880176343089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30314061178202027607163141 5683886470912880176343089)
                    ·
                      refine ⟨4262914853184660132257317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683886470912880176343089 4262914853184660132257317)
                      ·
                        rfl

theorem cell23_8301997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_8301997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8301997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8301997 prefixEnd_8301997 := by exact prefixLift 8301997
  have htrace : WordTrace (prefixWord ++ tailWord_8301997) baseStart_8301997 baseEnd_8301997 := by
    simpa [prefixWord, tailWord_8301997, baseEnd_8301997] using wordTrace_append hprefix tailTrace_8301997
  have hstable : (prefixWord ++ tailWord_8301997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8301997).length < 2 ^ (prefixWord ++ tailWord_8301997).sum := by decide
  have hdescent : baseEnd_8301997 < baseStart_8301997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8301997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302013 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_8302013 : Nat := 118140960795 + 8302013 * 2 ^ 59
def prefixEnd_8302013 : Nat := 4983230072969 + 3 ^ 40 * 8302013 * 2
def baseEnd_8302013 : Nat := 4262923068875132069657243

theorem tailTrace_8302013 : CollatzResearch.WordTrace tailWord_8302013 prefixEnd_8302013 4262923068875132069657243 := by
  unfold tailWord_8302013
  simp only [CollatzResearch.WordTrace]
  refine ⟨302799290072232246783038693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201866193381488164522025795 302799290072232246783038693)
  ·
    refine ⟨56774866888543546271819755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302799290072232246783038693 56774866888543546271819755)
    ·
      refine ⟨85162300332815319407729633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56774866888543546271819755 85162300332815319407729633)
      ·
        refine ⟨63871725249611489555797225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85162300332815319407729633 63871725249611489555797225)
        ·
          refine ⟨47903793937208617166847919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63871725249611489555797225 47903793937208617166847919)
          ·
            refine ⟨71855690905812925750271879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47903793937208617166847919 71855690905812925750271879)
            ·
              refine ⟨107783536358719388625407819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71855690905812925750271879 107783536358719388625407819)
              ·
                refine ⟨161675304538079082938111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107783536358719388625407819 161675304538079082938111729)
                ·
                  refine ⟨121256478403559312203583797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161675304538079082938111729 121256478403559312203583797)
                  ·
                    refine ⟨11367794850333685519085981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121256478403559312203583797 11367794850333685519085981)
                    ·
                      refine ⟨4262923068875132069657243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367794850333685519085981 4262923068875132069657243)
                      ·
                        rfl

theorem cell23_8302013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_8302013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302013 prefixEnd_8302013 := by exact prefixLift 8302013
  have htrace : WordTrace (prefixWord ++ tailWord_8302013) baseStart_8302013 baseEnd_8302013 := by
    simpa [prefixWord, tailWord_8302013, baseEnd_8302013] using wordTrace_append hprefix tailTrace_8302013
  have hstable : (prefixWord ++ tailWord_8302013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302013).length < 2 ^ (prefixWord ++ tailWord_8302013).sum := by decide
  have hdescent : baseEnd_8302013 < baseStart_8302013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302030 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_8302030 : Nat := 118140960795 + 8302030 * 2 ^ 59
def prefixEnd_8302030 : Nat := 4983230072969 + 3 ^ 40 * 8302030 * 2
def baseEnd_8302030 : Nat := 4262931798046258503144665

theorem tailTrace_8302030 : CollatzResearch.WordTrace tailWord_8302030 prefixEnd_8302030 4262931798046258503144665 := by
  unfold tailWord_8302030
  simp only [CollatzResearch.WordTrace]
  refine ⟨37849988764146332335800943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201866606742113772457605029 37849988764146332335800943)
  ·
    refine ⟨56774983146219498503701415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37849988764146332335800943 56774983146219498503701415)
    ·
      refine ⟨85162474719329247755552123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56774983146219498503701415 85162474719329247755552123)
      ·
        refine ⟨127743712078993871633328185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85162474719329247755552123 127743712078993871633328185)
        ·
          refine ⟨95807784059245403724996139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127743712078993871633328185 95807784059245403724996139)
          ·
            refine ⟨143711676088868105587494209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95807784059245403724996139 143711676088868105587494209)
            ·
              refine ⟨107783757066651079190620657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143711676088868105587494209 107783757066651079190620657)
              ·
                refine ⟨80837817799988309392965493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107783757066651079190620657 80837817799988309392965493)
                ·
                  refine ⟨7578545418748904005590515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80837817799988309392965493 7578545418748904005590515)
                  ·
                    refine ⟨11367818128123356008385773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7578545418748904005590515 11367818128123356008385773)
                    ·
                      refine ⟨4262931798046258503144665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367818128123356008385773 4262931798046258503144665)
                      ·
                        rfl

theorem cell23_8302030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_8302030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302030 prefixEnd_8302030 := by exact prefixLift 8302030
  have htrace : WordTrace (prefixWord ++ tailWord_8302030) baseStart_8302030 baseEnd_8302030 := by
    simpa [prefixWord, tailWord_8302030, baseEnd_8302030] using wordTrace_append hprefix tailTrace_8302030
  have hstable : (prefixWord ++ tailWord_8302030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302030).length < 2 ^ (prefixWord ++ tailWord_8302030).sum := by decide
  have hdescent : baseEnd_8302030 < baseStart_8302030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302040 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_8302040 : Nat := 118140960795 + 8302040 * 2 ^ 59
def prefixEnd_8302040 : Nat := 4983230072969 + 3 ^ 40 * 8302040 * 2
def baseEnd_8302040 : Nat := 4262936932852803464019619

theorem tailTrace_8302040 : CollatzResearch.WordTrace tailWord_8302040 prefixEnd_8302040 4262936932852803464019619 := by
  unfold tailWord_8302040
  simp only [CollatzResearch.WordTrace]
  refine ⟨151400137421567215197135787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201866849895422953596181049 151400137421567215197135787)
  ·
    refine ⟨227100206132350822795703681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151400137421567215197135787 227100206132350822795703681)
    ·
      refine ⟨170325154599263117096777761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227100206132350822795703681 170325154599263117096777761)
      ·
        refine ⟨127743865949447337822583321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170325154599263117096777761 127743865949447337822583321)
        ·
          refine ⟨95807899462085503366937491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127743865949447337822583321 95807899462085503366937491)
          ·
            refine ⟨143711849193128255050406237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95807899462085503366937491 143711849193128255050406237)
            ·
              refine ⟨53891943447423095643902339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143711849193128255050406237 53891943447423095643902339)
              ·
                refine ⟨80837915171134643465853509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53891943447423095643902339 80837915171134643465853509)
                ·
                  refine ⟨15157109094587745649847533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80837915171134643465853509 15157109094587745649847533)
                  ·
                    refine ⟨5683915910470404618692825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15157109094587745649847533 5683915910470404618692825)
                    ·
                      refine ⟨4262936932852803464019619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5683915910470404618692825 4262936932852803464019619)
                      ·
                        rfl

theorem cell23_8302040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_8302040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302040 prefixEnd_8302040 := by exact prefixLift 8302040
  have htrace : WordTrace (prefixWord ++ tailWord_8302040) baseStart_8302040 baseEnd_8302040 := by
    simpa [prefixWord, tailWord_8302040, baseEnd_8302040] using wordTrace_append hprefix tailTrace_8302040
  have hstable : (prefixWord ++ tailWord_8302040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302040).length < 2 ^ (prefixWord ++ tailWord_8302040).sum := by decide
  have hdescent : baseEnd_8302040 < baseStart_8302040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302084 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_8302084 : Nat := 118140960795 + 8302084 * 2 ^ 59
def prefixEnd_8302084 : Nat := 4983230072969 + 3 ^ 40 * 8302084 * 2
def baseEnd_8302084 : Nat := 1420986508667200430623139

theorem tailTrace_8302084 : CollatzResearch.WordTrace tailWord_8302084 prefixEnd_8302084 1420986508667200430623139 := by
  unfold tailWord_8302084
  simp only [CollatzResearch.WordTrace]
  refine ⟨151400939827487512954436653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201867919769983350605915537 151400939827487512954436653)
  ·
    refine ⟨56775352435307817357913745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151400939827487512954436653 56775352435307817357913745)
    ·
      refine ⟨42581514326480863018435309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56775352435307817357913745 42581514326480863018435309)
      ·
        refine ⟨15968067872430323631913241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42581514326480863018435309 15968067872430323631913241)
        ·
          refine ⟨11976050904322742723934931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968067872430323631913241 11976050904322742723934931)
          ·
            refine ⟨17964076356484114085902397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976050904322742723934931 17964076356484114085902397)
            ·
              refine ⟨6736528633681542782213399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17964076356484114085902397 6736528633681542782213399)
              ·
                refine ⟨10104792950522314173320099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736528633681542782213399 10104792950522314173320099)
                ·
                  refine ⟨15157189425783471259980149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104792950522314173320099 15157189425783471259980149)
                  ·
                    refine ⟨1420986508667200430623139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15157189425783471259980149 1420986508667200430623139)
                    ·
                      rfl

theorem cell23_8302084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_8302084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302084 prefixEnd_8302084 := by exact prefixLift 8302084
  have htrace : WordTrace (prefixWord ++ tailWord_8302084) baseStart_8302084 baseEnd_8302084 := by
    simpa [prefixWord, tailWord_8302084, baseEnd_8302084] using wordTrace_append hprefix tailTrace_8302084
  have hstable : (prefixWord ++ tailWord_8302084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302084).length < 2 ^ (prefixWord ++ tailWord_8302084).sum := by decide
  have hdescent : baseEnd_8302084 < baseStart_8302084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302090 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_8302090 : Nat := 118140960795 + 8302090 * 2 ^ 59
def prefixEnd_8302090 : Nat := 4983230072969 + 3 ^ 40 * 8302090 * 2
def baseEnd_8302090 : Nat := 4262962606885528268394389

theorem tailTrace_8302090 : CollatzResearch.WordTrace tailWord_8302090 prefixEnd_8302090 4262962606885528268394389 := by
  unfold tailWord_8302090
  simp only [CollatzResearch.WordTrace]
  refine ⟨75700524623238322233397931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201868065661968859289061149 75700524623238322233397931)
  ·
    refine ⟨113550786934857483350096897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75700524623238322233397931 113550786934857483350096897)
    ·
      refine ⟨85163090201143112512572673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113550786934857483350096897 85163090201143112512572673)
      ·
        refine ⟨63872317650857334384429505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85163090201143112512572673 63872317650857334384429505)
        ·
          refine ⟨47904238238143000788322129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63872317650857334384429505 47904238238143000788322129)
          ·
            refine ⟨35928178678607250591241597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47904238238143000788322129 35928178678607250591241597)
            ·
              refine ⟨13473067004477718971715599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35928178678607250591241597 13473067004477718971715599)
              ·
                refine ⟨20209600506716578457573399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13473067004477718971715599 20209600506716578457573399)
                ·
                  refine ⟨30314400760074867686360099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20209600506716578457573399 30314400760074867686360099)
                  ·
                    refine ⟨45471601140112301529540149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30314400760074867686360099 45471601140112301529540149)
                    ·
                      refine ⟨4262962606885528268394389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45471601140112301529540149 4262962606885528268394389)
                      ·
                        rfl

theorem cell23_8302090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_8302090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302090 prefixEnd_8302090 := by exact prefixLift 8302090
  have htrace : WordTrace (prefixWord ++ tailWord_8302090) baseStart_8302090 baseEnd_8302090 := by
    simpa [prefixWord, tailWord_8302090, baseEnd_8302090] using wordTrace_append hprefix tailTrace_8302090
  have hstable : (prefixWord ++ tailWord_8302090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302090).length < 2 ^ (prefixWord ++ tailWord_8302090).sum := by decide
  have hdescent : baseEnd_8302090 < baseStart_8302090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302141 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_8302141 : Nat := 118140960795 + 8302141 * 2 ^ 59
def prefixEnd_8302141 : Nat := 4983230072969 + 3 ^ 40 * 8302141 * 2
def baseEnd_8302141 : Nat := 4262988794398907568856655

theorem tailTrace_8302141 : CollatzResearch.WordTrace tailWord_8302141 prefixEnd_8302141 4262988794398907568856655 := by
  unfold tailWord_8302141
  simp only [CollatzResearch.WordTrace]
  refine ⟨302803958615768524643698277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201869305743845683095798851 302803958615768524643698277)
  ·
    refine ⟨56775742240456598370693427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302803958615768524643698277 56775742240456598370693427)
    ·
      refine ⟨85163613360684897556040141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56775742240456598370693427 85163613360684897556040141)
      ·
        refine ⟨31936355010256836583515053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85163613360684897556040141 31936355010256836583515053)
        ·
          refine ⟨11976133128846313718818145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31936355010256836583515053 11976133128846313718818145)
          ·
            refine ⟨8982099846634735289113609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11976133128846313718818145 8982099846634735289113609)
            ·
              refine ⟨6736574884976051466835207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8982099846634735289113609 6736574884976051466835207)
              ·
                refine ⟨10104862327464077200252811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736574884976051466835207 10104862327464077200252811)
                ·
                  refine ⟨15157293491196115800379217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104862327464077200252811 15157293491196115800379217)
                  ·
                    refine ⟨11367970118397086850284413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15157293491196115800379217 11367970118397086850284413)
                    ·
                      refine ⟨4262988794398907568856655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11367970118397086850284413 4262988794398907568856655)
                      ·
                        rfl

theorem cell23_8302141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_8302141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302141 prefixEnd_8302141 := by exact prefixLift 8302141
  have htrace : WordTrace (prefixWord ++ tailWord_8302141) baseStart_8302141 baseEnd_8302141 := by
    simpa [prefixWord, tailWord_8302141, baseEnd_8302141] using wordTrace_append hprefix tailTrace_8302141
  have hstable : (prefixWord ++ tailWord_8302141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302141).length < 2 ^ (prefixWord ++ tailWord_8302141).sum := by decide
  have hdescent : baseEnd_8302141 < baseStart_8302141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302194 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_8302194 : Nat := 118140960795 + 8302194 * 2 ^ 59
def prefixEnd_8302194 : Nat := 4983230072969 + 3 ^ 40 * 8302194 * 2
def baseEnd_8302194 : Nat := 4263016008873595861493911

theorem tailTrace_8302194 : CollatzResearch.WordTrace tailWord_8302194 prefixEnd_8302194 4263016008873595861493911 := by
  unfold tailWord_8302194
  simp only [CollatzResearch.WordTrace]
  refine ⟨75701472921144128673844409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201870594456384343130251757 75701472921144128673844409)
  ·
    refine ⟨56776104690858096505383307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75701472921144128673844409 56776104690858096505383307)
    ·
      refine ⟨85164157036287144758074961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56776104690858096505383307 85164157036287144758074961)
      ·
        refine ⟨63873117777215358568556221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85164157036287144758074961 63873117777215358568556221)
        ·
          refine ⟨23952419166455759463208583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63873117777215358568556221 23952419166455759463208583)
          ·
            refine ⟨35928628749683639194812875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23952419166455759463208583 35928628749683639194812875)
            ·
              refine ⟨53892943124525458792219313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35928628749683639194812875 53892943124525458792219313)
              ·
                refine ⟨40419707343394094094164485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53892943124525458792219313 40419707343394094094164485)
                ·
                  refine ⟨7578695126886392642655841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40419707343394094094164485 7578695126886392642655841)
                  ·
                    refine ⟨5684021345164794481991881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578695126886392642655841 5684021345164794481991881)
                    ·
                      refine ⟨4263016008873595861493911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684021345164794481991881 4263016008873595861493911)
                      ·
                        rfl

theorem cell23_8302194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_8302194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302194 prefixEnd_8302194 := by exact prefixLift 8302194
  have htrace : WordTrace (prefixWord ++ tailWord_8302194) baseStart_8302194 baseEnd_8302194 := by
    simpa [prefixWord, tailWord_8302194, baseEnd_8302194] using wordTrace_append hprefix tailTrace_8302194
  have hstable : (prefixWord ++ tailWord_8302194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302194).length < 2 ^ (prefixWord ++ tailWord_8302194).sum := by decide
  have hdescent : baseEnd_8302194 < baseStart_8302194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302197 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8302197 : Nat := 118140960795 + 8302197 * 2 ^ 59
def prefixEnd_8302197 : Nat := 4983230072969 + 3 ^ 40 * 8302197 * 2
def baseEnd_8302197 : Nat := 4263017549315559349756397

theorem tailTrace_8302197 : CollatzResearch.WordTrace tailWord_8302197 prefixEnd_8302197 4263017549315559349756397 := by
  unfold tailWord_8302197
  simp only [CollatzResearch.WordTrace]
  refine ⟨302806001103565646207736845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201870667402377097471824563 302806001103565646207736845)
  ·
    refine ⟨113552250413837117327901317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302806001103565646207736845 113552250413837117327901317)
    ·
      refine ⟨21291046952594459498981497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113552250413837117327901317 21291046952594459498981497)
      ·
        refine ⟨15968285214445844624236123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21291046952594459498981497 15968285214445844624236123)
        ·
          refine ⟨23952427821668766936354185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15968285214445844624236123 23952427821668766936354185)
          ·
            refine ⟨17964320866251575202265639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23952427821668766936354185 17964320866251575202265639)
            ·
              refine ⟨26946481299377362803398459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17964320866251575202265639 26946481299377362803398459)
              ·
                refine ⟨40419721949066044205097689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26946481299377362803398459 40419721949066044205097689)
                ·
                  refine ⟨30314791461799533153823267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40419721949066044205097689 30314791461799533153823267)
                  ·
                    refine ⟨45472187192699299730734901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30314791461799533153823267 45472187192699299730734901)
                    ·
                      refine ⟨4263017549315559349756397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45472187192699299730734901 4263017549315559349756397)
                      ·
                        rfl

theorem cell23_8302197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8302197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302197 prefixEnd_8302197 := by exact prefixLift 8302197
  have htrace : WordTrace (prefixWord ++ tailWord_8302197) baseStart_8302197 baseEnd_8302197 := by
    simpa [prefixWord, tailWord_8302197, baseEnd_8302197] using wordTrace_append hprefix tailTrace_8302197
  have hstable : (prefixWord ++ tailWord_8302197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302197).length < 2 ^ (prefixWord ++ tailWord_8302197).sum := by decide
  have hdescent : baseEnd_8302197 < baseStart_8302197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302228 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_8302228 : Nat := 118140960795 + 8302228 * 2 ^ 59
def prefixEnd_8302228 : Nat := 4983230072969 + 3 ^ 40 * 8302228 * 2
def baseEnd_8302228 : Nat := 4263033467215848728468755

theorem tailTrace_8302228 : CollatzResearch.WordTrace tailWord_8302228 prefixEnd_8302228 4263033467215848728468755 := by
  unfold tailWord_8302228
  simp only [CollatzResearch.WordTrace]
  refine ⟨151403565883226669251057669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201871421177635559001410225 151403565883226669251057669)
  ·
    refine ⟨28388168603105000484573313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151403565883226669251057669 28388168603105000484573313)
    ·
      refine ⟨21291126452328750363429985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28388168603105000484573313 21291126452328750363429985)
      ·
        refine ⟨15968344839246562772572489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21291126452328750363429985 15968344839246562772572489)
        ·
          refine ⟨11976258629434922079429367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15968344839246562772572489 11976258629434922079429367)
          ·
            refine ⟨17964387944152383119144051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976258629434922079429367 17964387944152383119144051)
            ·
              refine ⟨26946581916228574678716077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17964387944152383119144051 26946581916228574678716077)
              ·
                refine ⟨10104968218585715504518529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26946581916228574678716077 10104968218585715504518529)
                ·
                  refine ⟨7578726163939286628388897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10104968218585715504518529 7578726163939286628388897)
                  ·
                    refine ⟨5684044622954464971291673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578726163939286628388897 5684044622954464971291673)
                    ·
                      refine ⟨4263033467215848728468755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684044622954464971291673 4263033467215848728468755)
                      ·
                        rfl

theorem cell23_8302228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_8302228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302228 prefixEnd_8302228 := by exact prefixLift 8302228
  have htrace : WordTrace (prefixWord ++ tailWord_8302228) baseStart_8302228 baseEnd_8302228 := by
    simpa [prefixWord, tailWord_8302228, baseEnd_8302228] using wordTrace_append hprefix tailTrace_8302228
  have hstable : (prefixWord ++ tailWord_8302228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302228).length < 2 ^ (prefixWord ++ tailWord_8302228).sum := by decide
  have hdescent : baseEnd_8302228 < baseStart_8302228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302320 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_8302320 : Nat := 118140960795 + 8302320 * 2 ^ 59
def prefixEnd_8302320 : Nat := 4983230072969 + 3 ^ 40 * 8302320 * 2
def baseEnd_8302320 : Nat := 1421026902478687456172777

theorem tailTrace_8302320 : CollatzResearch.WordTrace tailWord_8302320 prefixEnd_8302320 1421026902478687456172777 := by
  unfold tailWord_8302320
  simp only [CollatzResearch.WordTrace]
  refine ⟨151405243641060019107232207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201873658188080025476309609 151405243641060019107232207)
  ·
    refine ⟨227107865461590028660848311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151405243641060019107232207 227107865461590028660848311)
    ·
      refine ⟨340661798192385042991272467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227107865461590028660848311 340661798192385042991272467)
      ·
        refine ⟨510992697288577564486908701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340661798192385042991272467 510992697288577564486908701)
        ·
          refine ⟨191622261483216586682590763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510992697288577564486908701 191622261483216586682590763)
          ·
            refine ⟨287433392224824880023886145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191622261483216586682590763 287433392224824880023886145)
            ·
              refine ⟨215575044168618660017914609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287433392224824880023886145 215575044168618660017914609)
              ·
                refine ⟨161681283126463995013435957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215575044168618660017914609 161681283126463995013435957)
                ·
                  refine ⟨15157620293105999532509621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161681283126463995013435957 15157620293105999532509621)
                  ·
                    refine ⟨1421026902478687456172777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15157620293105999532509621 1421026902478687456172777)
                    ·
                      rfl

theorem cell23_8302320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_8302320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302320 prefixEnd_8302320 := by exact prefixLift 8302320
  have htrace : WordTrace (prefixWord ++ tailWord_8302320) baseStart_8302320 baseEnd_8302320 := by
    simpa [prefixWord, tailWord_8302320, baseEnd_8302320] using wordTrace_append hprefix tailTrace_8302320
  have hstable : (prefixWord ++ tailWord_8302320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302320).length < 2 ^ (prefixWord ++ tailWord_8302320).sum := by decide
  have hdescent : baseEnd_8302320 < baseStart_8302320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302367 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 6, 4]
def baseStart_8302367 : Nat := 118140960795 + 8302367 * 2 ^ 59
def prefixEnd_8302367 : Nat := 4983230072969 + 3 ^ 40 * 8302367 * 2
def baseEnd_8302367 : Nat := 1421034947008941228210205

theorem tailTrace_8302367 : CollatzResearch.WordTrace tailWord_8302367 prefixEnd_8302367 1421034947008941228210205 := by
  unfold tailWord_8302367
  simp only [CollatzResearch.WordTrace]
  refine ⟨302812201512949765241425355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201874801008633176827616903 302812201512949765241425355)
  ·
    refine ⟨454218302269424647862138033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302812201512949765241425355 454218302269424647862138033)
    ·
      refine ⟨340663726702068485896603525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454218302269424647862138033 340663726702068485896603525)
      ·
        refine ⟨63874448756637841105613161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340663726702068485896603525 63874448756637841105613161)
        ·
          refine ⟨47905836567478380829209871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63874448756637841105613161 47905836567478380829209871)
          ·
            refine ⟨71858754851217571243814807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47905836567478380829209871 71858754851217571243814807)
            ·
              refine ⟨107788132276826356865722211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71858754851217571243814807 107788132276826356865722211)
              ·
                refine ⟨161682198415239535298583317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107788132276826356865722211 161682198415239535298583317)
                ·
                  refine ⟨7578853050714353217121093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161682198415239535298583317 7578853050714353217121093)
                  ·
                    refine ⟨1421034947008941228210205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7578853050714353217121093 1421034947008941228210205)
                    ·
                      rfl

theorem cell23_8302367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 4].length) (baseStart_8302367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302367 prefixEnd_8302367 := by exact prefixLift 8302367
  have htrace : WordTrace (prefixWord ++ tailWord_8302367) baseStart_8302367 baseEnd_8302367 := by
    simpa [prefixWord, tailWord_8302367, baseEnd_8302367] using wordTrace_append hprefix tailTrace_8302367
  have hstable : (prefixWord ++ tailWord_8302367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302367).length < 2 ^ (prefixWord ++ tailWord_8302367).sum := by decide
  have hdescent : baseEnd_8302367 < baseStart_8302367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302380 : List Nat := [2, 2, 1, 1, 1, 5, 11]
def baseStart_8302380 : Nat := 118140960795 + 8302380 * 2 ^ 59
def prefixEnd_8302380 : Nat := 4983230072969 + 3 ^ 40 * 8302380 * 2
def baseEnd_8302380 : Nat := 52631006373769532515655

theorem tailTrace_8302380 : CollatzResearch.WordTrace tailWord_8302380 prefixEnd_8302380 52631006373769532515655 := by
  unfold tailWord_8302380
  simp only [CollatzResearch.WordTrace]
  refine ⟨151406337830951334230824297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201875117107935112307765729 151406337830951334230824297)
  ·
    refine ⟨113554753373213500673118223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151406337830951334230824297 113554753373213500673118223)
    ·
      refine ⟨170332130059820251009677335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113554753373213500673118223 170332130059820251009677335)
      ·
        refine ⟨255498195089730376514516003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170332130059820251009677335 255498195089730376514516003)
        ·
          refine ⟨383247292634595564771774005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255498195089730376514516003 383247292634595564771774005)
          ·
            refine ⟨35929433684493334197353813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383247292634595564771774005 35929433684493334197353813)
            ·
              refine ⟨52631006373769532515655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35929433684493334197353813 52631006373769532515655)
              ·
                rfl

theorem cell23_8302380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 11].length) (baseStart_8302380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302380 prefixEnd_8302380 := by exact prefixLift 8302380
  have htrace : WordTrace (prefixWord ++ tailWord_8302380) baseStart_8302380 baseEnd_8302380 := by
    simpa [prefixWord, tailWord_8302380, baseEnd_8302380] using wordTrace_append hprefix tailTrace_8302380
  have hstable : (prefixWord ++ tailWord_8302380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302380).length < 2 ^ (prefixWord ++ tailWord_8302380).sum := by decide
  have hdescent : baseEnd_8302380 < baseStart_8302380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302397 : List Nat := [1, 4, 1, 4, 1, 1, 1, 10]
def baseStart_8302397 : Nat := 118140960795 + 8302397 * 2 ^ 59
def prefixEnd_8302397 : Nat := 4983230072969 + 3 ^ 40 * 8302397 * 2
def baseEnd_8302397 : Nat := 157893342423942909898351

theorem tailTrace_8302397 : CollatzResearch.WordTrace tailWord_8302397 prefixEnd_8302397 157893342423942909898351 := by
  unfold tailWord_8302397
  simp only [CollatzResearch.WordTrace]
  refine ⟨302813295702841080365017445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201875530468560720243344963 302813295702841080365017445)
  ·
    refine ⟨56777492944282702568440771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302813295702841080365017445 56777492944282702568440771)
    ·
      refine ⟨85166239416424053852661157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56777492944282702568440771 85166239416424053852661157)
      ·
        refine ⟨15968669890579510097373967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85166239416424053852661157 15968669890579510097373967)
        ·
          refine ⟨23953004835869265146060951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15968669890579510097373967 23953004835869265146060951)
          ·
            refine ⟨35929507253803897719091427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23953004835869265146060951 35929507253803897719091427)
            ·
              refine ⟨53894260880705846578637141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35929507253803897719091427 53894260880705846578637141)
              ·
                refine ⟨157893342423942909898351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53894260880705846578637141 157893342423942909898351)
                ·
                  rfl

theorem cell23_8302397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 10].length) (baseStart_8302397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302397 prefixEnd_8302397 := by exact prefixLift 8302397
  have htrace : WordTrace (prefixWord ++ tailWord_8302397) baseStart_8302397 baseEnd_8302397 := by
    simpa [prefixWord, tailWord_8302397, baseEnd_8302397] using wordTrace_append hprefix tailTrace_8302397
  have hstable : (prefixWord ++ tailWord_8302397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302397).length < 2 ^ (prefixWord ++ tailWord_8302397).sum := by decide
  have hdescent : baseEnd_8302397 < baseStart_8302397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302428 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_8302428 : Nat := 118140960795 + 8302428 * 2 ^ 59
def prefixEnd_8302428 : Nat := 4983230072969 + 3 ^ 40 * 8302428 * 2
def baseEnd_8302428 : Nat := 4263136163346747945967835

theorem tailTrace_8302428 : CollatzResearch.WordTrace tailWord_8302428 prefixEnd_8302428 4263136163346747945967835 := by
  unfold tailWord_8302428
  simp only [CollatzResearch.WordTrace]
  refine ⟨151407213182864386329697969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201876284243819181772930625 151407213182864386329697969)
  ·
    refine ⟨113555409887148289747273477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151407213182864386329697969 113555409887148289747273477)
    ·
      refine ⟨21291639353840304327613777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113555409887148289747273477 21291639353840304327613777)
      ·
        refine ⟨15968729515380228245710333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21291639353840304327613777 15968729515380228245710333)
        ·
          refine ⟨5988273568267585592141375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15968729515380228245710333 5988273568267585592141375)
          ·
            refine ⟨8982410352401378388212063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988273568267585592141375 8982410352401378388212063)
            ·
              refine ⟨13473615528602067582318095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982410352401378388212063 13473615528602067582318095)
              ·
                refine ⟨20210423292903101373477143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13473615528602067582318095 20210423292903101373477143)
                ·
                  refine ⟨30315634939354652060215715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20210423292903101373477143 30315634939354652060215715)
                  ·
                    refine ⟨45473452409031978090323573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30315634939354652060215715 45473452409031978090323573)
                    ·
                      refine ⟨4263136163346747945967835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45473452409031978090323573 4263136163346747945967835)
                      ·
                        rfl

theorem cell23_8302428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_8302428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302428 prefixEnd_8302428 := by exact prefixLift 8302428
  have htrace : WordTrace (prefixWord ++ tailWord_8302428) baseStart_8302428 baseEnd_8302428 := by
    simpa [prefixWord, tailWord_8302428, baseEnd_8302428] using wordTrace_append hprefix tailTrace_8302428
  have hstable : (prefixWord ++ tailWord_8302428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302428).length < 2 ^ (prefixWord ++ tailWord_8302428).sum := by decide
  have hdescent : baseEnd_8302428 < baseStart_8302428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302442 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_8302442 : Nat := 118140960795 + 8302442 * 2 ^ 59
def prefixEnd_8302442 : Nat := 4983230072969 + 3 ^ 40 * 8302442 * 2
def baseEnd_8302442 : Nat := 4263143352075910891192771

theorem tailTrace_8302442 : CollatzResearch.WordTrace tailWord_8302442 prefixEnd_8302442 4263143352075910891192771 := by
  unfold tailWord_8302442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75703734246919513262601395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201876624658452035366937053 75703734246919513262601395)
  ·
    refine ⟨113555601370379269893902093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75703734246919513262601395 113555601370379269893902093)
    ·
      refine ⟨42583350513892226210213285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113555601370379269893902093 42583350513892226210213285)
      ·
        refine ⟨7984378221354792414414991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42583350513892226210213285 7984378221354792414414991)
        ·
          refine ⟨11976567332032188621622487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984378221354792414414991 11976567332032188621622487)
          ·
            refine ⟨17964850998048282932433731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976567332032188621622487 17964850998048282932433731)
            ·
              refine ⟨26947276497072424398650597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17964850998048282932433731 26947276497072424398650597)
              ·
                refine ⟨5052614343201079574746987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26947276497072424398650597 5052614343201079574746987)
                ·
                  refine ⟨7578921514801619362120481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052614343201079574746987 7578921514801619362120481)
                  ·
                    refine ⟨5684191136101214521590361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578921514801619362120481 5684191136101214521590361)
                    ·
                      refine ⟨4263143352075910891192771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684191136101214521590361 4263143352075910891192771)
                      ·
                        rfl

theorem cell23_8302442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_8302442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302442 prefixEnd_8302442 := by exact prefixLift 8302442
  have htrace : WordTrace (prefixWord ++ tailWord_8302442) baseStart_8302442 baseEnd_8302442 := by
    simpa [prefixWord, tailWord_8302442, baseEnd_8302442] using wordTrace_append hprefix tailTrace_8302442
  have hstable : (prefixWord ++ tailWord_8302442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302442).length < 2 ^ (prefixWord ++ tailWord_8302442).sum := by decide
  have hdescent : baseEnd_8302442 < baseStart_8302442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302457 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_8302457 : Nat := 118140960795 + 8302457 * 2 ^ 59
def prefixEnd_8302457 : Nat := 4983230072969 + 3 ^ 40 * 8302457 * 2
def baseEnd_8302457 : Nat := 1421050351428576110835067

theorem tailTrace_8302457 : CollatzResearch.WordTrace tailWord_8302457 prefixEnd_8302457 1421050351428576110835067 := by
  unfold tailWord_8302457
  simp only [CollatzResearch.WordTrace]
  refine ⟨302815484082623710612201625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201876989388415807074801083 302815484082623710612201625)
  ·
    refine ⟨227111613061967782959151219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302815484082623710612201625 227111613061967782959151219)
    ·
      refine ⟨340667419592951674438726829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227111613061967782959151219 340667419592951674438726829)
      ·
        refine ⟨127750282347356877914522561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340667419592951674438726829 127750282347356877914522561)
        ·
          refine ⟨95812711760517658435891921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127750282347356877914522561 95812711760517658435891921)
          ·
            refine ⟨71859533820388243826918941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95812711760517658435891921 71859533820388243826918941)
            ·
              refine ⟨26947325182645591435094603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71859533820388243826918941 26947325182645591435094603)
              ·
                refine ⟨40420987773968387152641905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26947325182645591435094603 40420987773968387152641905)
                ·
                  refine ⟨30315740830476290364481429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40420987773968387152641905 30315740830476290364481429)
                  ·
                    refine ⟨1421050351428576110835067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30315740830476290364481429 1421050351428576110835067)
                    ·
                      rfl

theorem cell23_8302457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_8302457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302457 prefixEnd_8302457 := by exact prefixLift 8302457
  have htrace : WordTrace (prefixWord ++ tailWord_8302457) baseStart_8302457 baseEnd_8302457 := by
    simpa [prefixWord, tailWord_8302457, baseEnd_8302457] using wordTrace_append hprefix tailTrace_8302457
  have hstable : (prefixWord ++ tailWord_8302457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302457).length < 2 ^ (prefixWord ++ tailWord_8302457).sum := by decide
  have hdescent : baseEnd_8302457 < baseStart_8302457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302615 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 1, 4]
def baseStart_8302615 : Nat := 118140960795 + 8302615 * 2 ^ 59
def prefixEnd_8302615 : Nat := 4983230072969 + 3 ^ 40 * 8302615 * 2
def baseEnd_8302615 : Nat := 1421077394743046238109825

theorem tailTrace_8302615 : CollatzResearch.WordTrace tailWord_8302615 prefixEnd_8302615 1421077394743046238109825 := by
  unfold tailWord_8302615
  simp only [CollatzResearch.WordTrace]
  refine ⟨302821246816051303596453299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201880831210700869064302199 302821246816051303596453299)
  ·
    refine ⟨454231870224076955394679949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302821246816051303596453299 454231870224076955394679949)
    ·
      refine ⟨170336951334028858273004981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454231870224076955394679949 170336951334028858273004981)
      ·
        refine ⟨15969089187565205463094217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170336951334028858273004981 15969089187565205463094217)
        ·
          refine ⟨11976816890673904097320663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15969089187565205463094217 11976816890673904097320663)
          ·
            refine ⟨17965225336010856145980995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976816890673904097320663 17965225336010856145980995)
            ·
              refine ⟨26947838004016284218971493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965225336010856145980995 26947838004016284218971493)
              ·
                refine ⟨5052719625753053291057155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26947838004016284218971493 5052719625753053291057155)
                ·
                  refine ⟨7579079438629579936585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052719625753053291057155 7579079438629579936585733)
                  ·
                    refine ⟨1421077394743046238109825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579079438629579936585733 1421077394743046238109825)
                    ·
                      rfl

theorem cell23_8302615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_8302615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302615 prefixEnd_8302615 := by exact prefixLift 8302615
  have htrace : WordTrace (prefixWord ++ tailWord_8302615) baseStart_8302615 baseEnd_8302615 := by
    simpa [prefixWord, tailWord_8302615, baseEnd_8302615] using wordTrace_append hprefix tailTrace_8302615
  have hstable : (prefixWord ++ tailWord_8302615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302615).length < 2 ^ (prefixWord ++ tailWord_8302615).sum := by decide
  have hdescent : baseEnd_8302615 < baseStart_8302615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302638 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_8302638 : Nat := 118140960795 + 8302638 * 2 ^ 59
def prefixEnd_8302638 : Nat := 4983230072969 + 3 ^ 40 * 8302638 * 2
def baseEnd_8302638 : Nat := 4263243994284192124341869

theorem tailTrace_8302638 : CollatzResearch.WordTrace tailWord_8302638 prefixEnd_8302638 4263243994284192124341869 := by
  unfold tailWord_8302638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37852760711870997315567571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201881390463311985683027045 37852760711870997315567571)
  ·
    refine ⟨56779141067806495973351357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37852760711870997315567571 56779141067806495973351357)
    ·
      refine ⟨21292177900427435990006759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56779141067806495973351357 21292177900427435990006759)
      ·
        refine ⟨31938266850641153985010139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21292177900427435990006759 31938266850641153985010139)
        ·
          refine ⟨47907400275961730977515209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31938266850641153985010139 47907400275961730977515209)
          ·
            refine ⟨35930550206971298233136407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47907400275961730977515209 35930550206971298233136407)
            ·
              refine ⟨53895825310456947349704611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35930550206971298233136407 53895825310456947349704611)
              ·
                refine ⟨80843737965685421024556917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53895825310456947349704611 80843737965685421024556917)
                ·
                  refine ⟨7579100434283008221052211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80843737965685421024556917 7579100434283008221052211)
                  ·
                    refine ⟨11368650651424512331578317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7579100434283008221052211 11368650651424512331578317)
                    ·
                      refine ⟨4263243994284192124341869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11368650651424512331578317 4263243994284192124341869)
                      ·
                        rfl

theorem cell23_8302638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_8302638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302638 prefixEnd_8302638 := by exact prefixLift 8302638
  have htrace : WordTrace (prefixWord ++ tailWord_8302638) baseStart_8302638 baseEnd_8302638 := by
    simpa [prefixWord, tailWord_8302638, baseEnd_8302638] using wordTrace_append hprefix tailTrace_8302638
  have hstable : (prefixWord ++ tailWord_8302638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302638).length < 2 ^ (prefixWord ++ tailWord_8302638).sum := by decide
  have hdescent : baseEnd_8302638 < baseStart_8302638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302648 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_8302648 : Nat := 118140960795 + 8302648 * 2 ^ 59
def prefixEnd_8302648 : Nat := 4983230072969 + 3 ^ 40 * 8302648 * 2
def baseEnd_8302648 : Nat := 4263249129090737085216823

theorem tailTrace_8302648 : CollatzResearch.WordTrace tailWord_8302648 prefixEnd_8302648 4263249129090737085216823 := by
  unfold tailWord_8302648
  simp only [CollatzResearch.WordTrace]
  refine ⟨151411225212465875116202299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201881633616621166821603065 151411225212465875116202299)
  ·
    refine ⟨227116837818698812674303449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151411225212465875116202299 227116837818698812674303449)
    ·
      refine ⟨170337628364024109505727587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227116837818698812674303449 170337628364024109505727587)
      ·
        refine ⟨255506442546036164258591381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170337628364024109505727587 255506442546036164258591381)
        ·
          refine ⟨11976864494345445199621471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255506442546036164258591381 11976864494345445199621471)
          ·
            refine ⟨17965296741518167799432207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11976864494345445199621471 17965296741518167799432207)
            ·
              refine ⟨26947945112277251699148311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965296741518167799432207 26947945112277251699148311)
              ·
                refine ⟨40421917668415877548722467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26947945112277251699148311 40421917668415877548722467)
                ·
                  refine ⟨60632876502623816323083701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40421917668415877548722467 60632876502623816323083701)
                  ·
                    refine ⟨5684332172120982780289097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60632876502623816323083701 5684332172120982780289097)
                    ·
                      refine ⟨4263249129090737085216823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684332172120982780289097 4263249129090737085216823)
                      ·
                        rfl

theorem cell23_8302648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_8302648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302648 prefixEnd_8302648 := by exact prefixLift 8302648
  have htrace : WordTrace (prefixWord ++ tailWord_8302648) baseStart_8302648 baseEnd_8302648 := by
    simpa [prefixWord, tailWord_8302648, baseEnd_8302648] using wordTrace_append hprefix tailTrace_8302648
  have hstable : (prefixWord ++ tailWord_8302648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302648).length < 2 ^ (prefixWord ++ tailWord_8302648).sum := by decide
  have hdescent : baseEnd_8302648 < baseStart_8302648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302691 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4]
def baseStart_8302691 : Nat := 118140960795 + 8302691 * 2 ^ 59
def prefixEnd_8302691 : Nat := 4983230072969 + 3 ^ 40 * 8302691 * 2
def baseEnd_8302691 : Nat := 4263271208758880416979125

theorem tailTrace_8302691 : CollatzResearch.WordTrace tailWord_8302691 prefixEnd_8302691 4263271208758880416979125 := by
  unfold tailWord_8302691
  simp only [CollatzResearch.WordTrace]
  refine ⟨302824018763775968576219927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201882679175850645717479951 302824018763775968576219927)
  ·
    refine ⟨454236028145663952864329891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302824018763775968576219927 454236028145663952864329891)
    ·
      refine ⟨681354042218495929296494837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454236028145663952864329891 681354042218495929296494837)
      ·
        refine ⟨63876941457983993371546391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 681354042218495929296494837 63876941457983993371546391)
        ·
          refine ⟨95815412186975990057319587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63876941457983993371546391 95815412186975990057319587)
          ·
            refine ⟨143723118280463985085979381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95815412186975990057319587 143723118280463985085979381)
            ·
              refine ⟨13474042338793498601810567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143723118280463985085979381 13474042338793498601810567)
              ·
                refine ⟨20211063508190247902715851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474042338793498601810567 20211063508190247902715851)
                ·
                  refine ⟨30316595262285371854073777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20211063508190247902715851 30316595262285371854073777)
                  ·
                    refine ⟨22737446446714028890555333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30316595262285371854073777 22737446446714028890555333)
                    ·
                      refine ⟨4263271208758880416979125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22737446446714028890555333 4263271208758880416979125)
                      ·
                        rfl

theorem cell23_8302691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_8302691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302691 prefixEnd_8302691 := by exact prefixLift 8302691
  have htrace : WordTrace (prefixWord ++ tailWord_8302691) baseStart_8302691 baseEnd_8302691 := by
    simpa [prefixWord, tailWord_8302691, baseEnd_8302691] using wordTrace_append hprefix tailTrace_8302691
  have hstable : (prefixWord ++ tailWord_8302691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302691).length < 2 ^ (prefixWord ++ tailWord_8302691).sum := by decide
  have hdescent : baseEnd_8302691 < baseStart_8302691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302764 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_8302764 : Nat := 118140960795 + 8302764 * 2 ^ 59
def prefixEnd_8302764 : Nat := 4983230072969 + 3 ^ 40 * 8302764 * 2
def baseEnd_8302764 : Nat := 4263308692846658631366289

theorem tailTrace_8302764 : CollatzResearch.WordTrace tailWord_8302764 prefixEnd_8302764 4263308692846658631366289 := by
  unfold tailWord_8302764
  simp only [CollatzResearch.WordTrace]
  refine ⟨151413340646255751021813673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201884454195007668029084897 151413340646255751021813673)
  ·
    refine ⟨113560005484691813266360255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151413340646255751021813673 113560005484691813266360255)
    ·
      refine ⟨170340008227037719899540383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113560005484691813266360255 170340008227037719899540383)
      ·
        refine ⟨255510012340556579849310575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170340008227037719899540383 255510012340556579849310575)
        ·
          refine ⟨383265018510834869773965863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255510012340556579849310575 383265018510834869773965863)
          ·
            refine ⟨574897527766252304660948795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383265018510834869773965863 574897527766252304660948795)
            ·
              refine ⟨862346291649378456991423193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574897527766252304660948795 862346291649378456991423193)
              ·
                refine ⟨646759718737033842743567395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862346291649378456991423193 646759718737033842743567395)
                ·
                  refine ⟨970139578105550764115351093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646759718737033842743567395 970139578105550764115351093)
                  ·
                    refine ⟨90950585447395384135814165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 970139578105550764115351093 90950585447395384135814165)
                    ·
                      refine ⟨4263308692846658631366289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90950585447395384135814165 4263308692846658631366289)
                      ·
                        rfl

theorem cell23_8302764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_8302764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302764 prefixEnd_8302764 := by exact prefixLift 8302764
  have htrace : WordTrace (prefixWord ++ tailWord_8302764) baseStart_8302764 baseEnd_8302764 := by
    simpa [prefixWord, tailWord_8302764, baseEnd_8302764] using wordTrace_append hprefix tailTrace_8302764
  have hstable : (prefixWord ++ tailWord_8302764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302764).length < 2 ^ (prefixWord ++ tailWord_8302764).sum := by decide
  have hdescent : baseEnd_8302764 < baseStart_8302764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302781 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_8302781 : Nat := 118140960795 + 8302781 * 2 ^ 59
def prefixEnd_8302781 : Nat := 4983230072969 + 3 ^ 40 * 8302781 * 2
def baseEnd_8302781 : Nat := 4263317422017785064853711

theorem tailTrace_8302781 : CollatzResearch.WordTrace tailWord_8302781 prefixEnd_8302781 4263317422017785064853711 := by
  unfold tailWord_8302781
  simp only [CollatzResearch.WordTrace]
  refine ⟨302827301333449913946996197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201884867555633275964664131 302827301333449913946996197)
  ·
    refine ⟨56780119000021858865061787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302827301333449913946996197 56780119000021858865061787)
    ·
      refine ⟨85170178500032788297592681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56780119000021858865061787 85170178500032788297592681)
      ·
        refine ⟨63877633875024591223194511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85170178500032788297592681 63877633875024591223194511)
        ·
          refine ⟨95816450812536886834791767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63877633875024591223194511 95816450812536886834791767)
          ·
            refine ⟨143724676218805330252187651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95816450812536886834791767 143724676218805330252187651)
            ·
              refine ⟨215587014328207995378281477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143724676218805330252187651 215587014328207995378281477)
              ·
                refine ⟨40422565186538999133427777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215587014328207995378281477 40422565186538999133427777)
                ·
                  refine ⟨30316923889904249350070833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40422565186538999133427777 30316923889904249350070833)
                  ·
                    refine ⟨22737692917428187012553125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30316923889904249350070833 22737692917428187012553125)
                    ·
                      refine ⟨4263317422017785064853711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22737692917428187012553125 4263317422017785064853711)
                      ·
                        rfl

theorem cell23_8302781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_8302781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302781 prefixEnd_8302781 := by exact prefixLift 8302781
  have htrace : WordTrace (prefixWord ++ tailWord_8302781) baseStart_8302781 baseEnd_8302781 := by
    simpa [prefixWord, tailWord_8302781, baseEnd_8302781] using wordTrace_append hprefix tailTrace_8302781
  have hstable : (prefixWord ++ tailWord_8302781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302781).length < 2 ^ (prefixWord ++ tailWord_8302781).sum := by decide
  have hdescent : baseEnd_8302781 < baseStart_8302781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302788 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_8302788 : Nat := 118140960795 + 8302788 * 2 ^ 59
def prefixEnd_8302788 : Nat := 4983230072969 + 3 ^ 40 * 8302788 * 2
def baseEnd_8302788 : Nat := 4263321016382366537466179

theorem tailTrace_8302788 : CollatzResearch.WordTrace tailWord_8302788 prefixEnd_8302788 4263321016382366537466179 := by
  unfold tailWord_8302788
  simp only [CollatzResearch.WordTrace]
  refine ⟨151413778322212277071250509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201885037762949702761667345 151413778322212277071250509)
  ·
    refine ⟨56780166870829603901718941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151413778322212277071250509 56780166870829603901718941)
    ·
      refine ⟨21292562576561101463144603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56780166870829603901718941 21292562576561101463144603)
      ·
        refine ⟨31938843864841652194716905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21292562576561101463144603 31938843864841652194716905)
        ·
          refine ⟨23954132898631239146037679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31938843864841652194716905 23954132898631239146037679)
          ·
            refine ⟨35931199347946858719056519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23954132898631239146037679 35931199347946858719056519)
            ·
              refine ⟨53896799021920288078584779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35931199347946858719056519 53896799021920288078584779)
              ·
                refine ⟨80845198532880432117877169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53896799021920288078584779 80845198532880432117877169)
                ·
                  refine ⟨60633898899660324088407877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80845198532880432117877169 60633898899660324088407877)
                  ·
                    refine ⟨11368856043686310766576477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60633898899660324088407877 11368856043686310766576477)
                    ·
                      refine ⟨4263321016382366537466179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11368856043686310766576477 4263321016382366537466179)
                      ·
                        rfl

theorem cell23_8302788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_8302788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302788 prefixEnd_8302788 := by exact prefixLift 8302788
  have htrace : WordTrace (prefixWord ++ tailWord_8302788) baseStart_8302788 baseEnd_8302788 := by
    simpa [prefixWord, tailWord_8302788, baseEnd_8302788] using wordTrace_append hprefix tailTrace_8302788
  have hstable : (prefixWord ++ tailWord_8302788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302788).length < 2 ^ (prefixWord ++ tailWord_8302788).sum := by decide
  have hdescent : baseEnd_8302788 < baseStart_8302788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302798 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_8302798 : Nat := 118140960795 + 8302798 * 2 ^ 59
def prefixEnd_8302798 : Nat := 4983230072969 + 3 ^ 40 * 8302798 * 2
def baseEnd_8302798 : Nat := 4263326151188911498341133

theorem tailTrace_8302798 : CollatzResearch.WordTrace tailWord_8302798 prefixEnd_8302798 4263326151188911498341133 := by
  unfold tailWord_8302798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37853490171798540731295631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201885280916258883900243365 37853490171798540731295631)
  ·
    refine ⟨56780235257697811096943447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37853490171798540731295631 56780235257697811096943447)
    ·
      refine ⟨85170352886546716645415171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56780235257697811096943447 85170352886546716645415171)
      ·
        refine ⟨127755529329820074968122757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85170352886546716645415171 127755529329820074968122757)
        ·
          refine ⟨23954161749341264056523017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127755529329820074968122757 23954161749341264056523017)
          ·
            refine ⟨17965621312005948042392263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23954161749341264056523017 17965621312005948042392263)
            ·
              refine ⟨26948431968008922063588395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965621312005948042392263 26948431968008922063588395)
              ·
                refine ⟨40422647952013383095382593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26948431968008922063588395 40422647952013383095382593)
                ·
                  refine ⟨30316985964010037321536945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40422647952013383095382593 30316985964010037321536945)
                  ·
                    refine ⟨22737739473007527991152709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30316985964010037321536945 22737739473007527991152709)
                    ·
                      refine ⟨4263326151188911498341133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22737739473007527991152709 4263326151188911498341133)
                      ·
                        rfl

theorem cell23_8302798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_8302798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302798 prefixEnd_8302798 := by exact prefixLift 8302798
  have htrace : WordTrace (prefixWord ++ tailWord_8302798) baseStart_8302798 baseEnd_8302798 := by
    simpa [prefixWord, tailWord_8302798, baseEnd_8302798] using wordTrace_append hprefix tailTrace_8302798
  have hstable : (prefixWord ++ tailWord_8302798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302798).length < 2 ^ (prefixWord ++ tailWord_8302798).sum := by decide
  have hdescent : baseEnd_8302798 < baseStart_8302798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302801 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_8302801 : Nat := 118140960795 + 8302801 * 2 ^ 59
def prefixEnd_8302801 : Nat := 4983230072969 + 3 ^ 40 * 8302801 * 2
def baseEnd_8302801 : Nat := 4263327691630874986603619

theorem tailTrace_8302801 : CollatzResearch.WordTrace tailWord_8302801 prefixEnd_8302801 4263327691630874986603619 := by
  unfold tailWord_8302801
  simp only [CollatzResearch.WordTrace]
  refine ⟨302828030793377457362724257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201885353862251638241816171 302828030793377457362724257)
  ·
    refine ⟨227121023095033093022043193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302828030793377457362724257 227121023095033093022043193)
    ·
      refine ⟨170340767321274819766532395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227121023095033093022043193 170340767321274819766532395)
      ·
        refine ⟨255511150981912229649798593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170340767321274819766532395 255511150981912229649798593)
        ·
          refine ⟨191633363236434172237348945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255511150981912229649798593 191633363236434172237348945)
          ·
            refine ⟨143725022427325629178011709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191633363236434172237348945 143725022427325629178011709)
            ·
              refine ⟨53896883410247110941754391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143725022427325629178011709 53896883410247110941754391)
              ·
                refine ⟨80845325115370666412631587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53896883410247110941754391 80845325115370666412631587)
                ·
                  refine ⟨121267987673055999618947381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80845325115370666412631587 121267987673055999618947381)
                  ·
                    refine ⟨11368873844348999964276317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121267987673055999618947381 11368873844348999964276317)
                    ·
                      refine ⟨4263327691630874986603619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11368873844348999964276317 4263327691630874986603619)
                      ·
                        rfl

theorem cell23_8302801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_8302801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302801 prefixEnd_8302801 := by exact prefixLift 8302801
  have htrace : WordTrace (prefixWord ++ tailWord_8302801) baseStart_8302801 baseEnd_8302801 := by
    simpa [prefixWord, tailWord_8302801, baseEnd_8302801] using wordTrace_append hprefix tailTrace_8302801
  have hstable : (prefixWord ++ tailWord_8302801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302801).length < 2 ^ (prefixWord ++ tailWord_8302801).sum := by decide
  have hdescent : baseEnd_8302801 < baseStart_8302801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302802 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_8302802 : Nat := 118140960795 + 8302802 * 2 ^ 59
def prefixEnd_8302802 : Nat := 4983230072969 + 3 ^ 40 * 8302802 * 2
def baseEnd_8302802 : Nat := 4263328205111529482691115

theorem tailTrace_8302802 : CollatzResearch.WordTrace tailWord_8302802 prefixEnd_8302802 4263328205111529482691115 := by
  unfold tailWord_8302802
  simp only [CollatzResearch.WordTrace]
  refine ⟨75707016816593458633377665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201885378177582556355673773 75707016816593458633377665)
  ·
    refine ⟨56780262612445093975033249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75707016816593458633377665 56780262612445093975033249)
    ·
      refine ⟨42585196959333820481274937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56780262612445093975033249 42585196959333820481274937)
      ·
        refine ⟨31938897719500365360956203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42585196959333820481274937 31938897719500365360956203)
        ·
          refine ⟨47908346579250548041434305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31938897719500365360956203 47908346579250548041434305)
          ·
            refine ⟨35931259934437911031075729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47908346579250548041434305 35931259934437911031075729)
            ·
              refine ⟨26948444950828433273306797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35931259934437911031075729 26948444950828433273306797)
              ·
                refine ⟨10105666856560662477490049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26948444950828433273306797 10105666856560662477490049)
                ·
                  refine ⟨7579250142420496858117537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10105666856560662477490049 7579250142420496858117537)
                  ·
                    refine ⟨5684437606815372643588153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579250142420496858117537 5684437606815372643588153)
                    ·
                      refine ⟨4263328205111529482691115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684437606815372643588153 4263328205111529482691115)
                      ·
                        rfl

theorem cell23_8302802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_8302802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302802 prefixEnd_8302802 := by exact prefixLift 8302802
  have htrace : WordTrace (prefixWord ++ tailWord_8302802) baseStart_8302802 baseEnd_8302802 := by
    simpa [prefixWord, tailWord_8302802, baseEnd_8302802] using wordTrace_append hprefix tailTrace_8302802
  have hstable : (prefixWord ++ tailWord_8302802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302802).length < 2 ^ (prefixWord ++ tailWord_8302802).sum := by decide
  have hdescent : baseEnd_8302802 < baseStart_8302802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302838 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_8302838 : Nat := 118140960795 + 8302838 * 2 ^ 59
def prefixEnd_8302838 : Nat := 4983230072969 + 3 ^ 40 * 8302838 * 2
def baseEnd_8302838 : Nat := 1421115563471697113946983

theorem tailTrace_8302838 : CollatzResearch.WordTrace tailWord_8302838 prefixEnd_8302838 1421115563471697113946983 := by
  unfold tailWord_8302838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926836268390213292613823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201886253529495608454547445 18926836268390213292613823)
  ·
    refine ⟨28390254402585319938920735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18926836268390213292613823 28390254402585319938920735)
    ·
      refine ⟨42585381603877979908381103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28390254402585319938920735 42585381603877979908381103)
      ·
        refine ⟨63878072405816969862571655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42585381603877979908381103 63878072405816969862571655)
        ·
          refine ⟨95817108608725454793857483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63878072405816969862571655 95817108608725454793857483)
          ·
            refine ⟨143725662913088182190786225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95817108608725454793857483 143725662913088182190786225)
            ·
              refine ⟨107794247184816136643089669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143725662913088182190786225 107794247184816136643089669)
              ·
                refine ⟨20211421347153025620579313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107794247184816136643089669 20211421347153025620579313)
                ·
                  refine ⟨15158566010364769215434485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20211421347153025620579313 15158566010364769215434485)
                  ·
                    refine ⟨1421115563471697113946983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15158566010364769215434485 1421115563471697113946983)
                    ·
                      rfl

theorem cell23_8302838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_8302838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302838 prefixEnd_8302838 := by exact prefixLift 8302838
  have htrace : WordTrace (prefixWord ++ tailWord_8302838) baseStart_8302838 baseEnd_8302838 := by
    simpa [prefixWord, tailWord_8302838, baseEnd_8302838] using wordTrace_append hprefix tailTrace_8302838
  have hstable : (prefixWord ++ tailWord_8302838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302838).length < 2 ^ (prefixWord ++ tailWord_8302838).sum := by decide
  have hdescent : baseEnd_8302838 < baseStart_8302838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302881 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 8]
def baseStart_8302881 : Nat := 118140960795 + 8302881 * 2 ^ 59
def prefixEnd_8302881 : Nat := 4983230072969 + 3 ^ 40 * 8302881 * 2
def baseEnd_8302881 : Nat := 473707641120359408178139

theorem tailTrace_8302881 : CollatzResearch.WordTrace tailWord_8302881 prefixEnd_8302881 473707641120359408178139 := by
  unfold tailWord_8302881
  simp only [CollatzResearch.WordTrace]
  refine ⟨302830948633087631025636497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201887299088725087350424331 302830948633087631025636497)
  ·
    refine ⟨227123211474815723269227373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302830948633087631025636497 227123211474815723269227373)
    ·
      refine ⟨85171204303055896225960265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227123211474815723269227373 85171204303055896225960265)
      ·
        refine ⟨63878403227291922169470199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85171204303055896225960265 63878403227291922169470199)
        ·
          refine ⟨95817604840937883254205299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63878403227291922169470199 95817604840937883254205299)
          ·
            refine ⟨143726407261406824881307949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95817604840937883254205299 143726407261406824881307949)
            ·
              refine ⟨53897402723027559330490481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143726407261406824881307949 53897402723027559330490481)
              ·
                refine ⟨40423052042270669497867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53897402723027559330490481 40423052042270669497867861)
                ·
                  refine ⟨473707641120359408178139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40423052042270669497867861 473707641120359408178139)
                  ·
                    rfl

theorem cell23_8302881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_8302881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302881 prefixEnd_8302881 := by exact prefixLift 8302881
  have htrace : WordTrace (prefixWord ++ tailWord_8302881) baseStart_8302881 baseEnd_8302881 := by
    simpa [prefixWord, tailWord_8302881, baseEnd_8302881] using wordTrace_append hprefix tailTrace_8302881
  have hstable : (prefixWord ++ tailWord_8302881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302881).length < 2 ^ (prefixWord ++ tailWord_8302881).sum := by decide
  have hdescent : baseEnd_8302881 < baseStart_8302881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302928 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_8302928 : Nat := 118140960795 + 8302928 * 2 ^ 59
def prefixEnd_8302928 : Nat := 4983230072969 + 3 ^ 40 * 8302928 * 2
def baseEnd_8302928 : Nat := 1421130967891331996571845

theorem tailTrace_8302928 : CollatzResearch.WordTrace tailWord_8302928 prefixEnd_8302928 1421130967891331996571845 := by
  unfold tailWord_8302928
  simp only [CollatzResearch.WordTrace]
  refine ⟨151416331431958679026298719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201888441909278238701731625 151416331431958679026298719)
  ·
    refine ⟨227124497147938018539448079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151416331431958679026298719 227124497147938018539448079)
    ·
      refine ⟨340686745721907027809172119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227124497147938018539448079 340686745721907027809172119)
      ·
        refine ⟨511030118582860541713758179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340686745721907027809172119 511030118582860541713758179)
        ·
          refine ⟨766545177874290812570637269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511030118582860541713758179 766545177874290812570637269)
          ·
            refine ⟨17965902606428690919624311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 766545177874290812570637269 17965902606428690919624311)
            ·
              refine ⟨26948853909643036379436467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965902606428690919624311 26948853909643036379436467)
              ·
                refine ⟨40423280864464554569154701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26948853909643036379436467 40423280864464554569154701)
                ·
                  refine ⟨15158730324174207963433013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40423280864464554569154701 15158730324174207963433013)
                  ·
                    refine ⟨1421130967891331996571845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15158730324174207963433013 1421130967891331996571845)
                    ·
                      rfl

theorem cell23_8302928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_8302928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302928 prefixEnd_8302928 := by exact prefixLift 8302928
  have htrace : WordTrace (prefixWord ++ tailWord_8302928) baseStart_8302928 baseEnd_8302928 := by
    simpa [prefixWord, tailWord_8302928, baseEnd_8302928] using wordTrace_append hprefix tailTrace_8302928
  have hstable : (prefixWord ++ tailWord_8302928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302928).length < 2 ^ (prefixWord ++ tailWord_8302928).sum := by decide
  have hdescent : baseEnd_8302928 < baseStart_8302928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302952 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_8302952 : Nat := 118140960795 + 8302952 * 2 ^ 59
def prefixEnd_8302952 : Nat := 4983230072969 + 3 ^ 40 * 8302952 * 2
def baseEnd_8302952 : Nat := 4263405227209703895815425

theorem tailTrace_8302952 : CollatzResearch.WordTrace tailWord_8302952 prefixEnd_8302952 4263405227209703895815425 := by
  unfold tailWord_8302952
  simp only [CollatzResearch.WordTrace]
  refine ⟨151416769107915205075735555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201889025477220273434314073 151416769107915205075735555)
  ·
    refine ⟨227125153661872807613603333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151416769107915205075735555 227125153661872807613603333)
    ·
      refine ⟨42585966311601151427550625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227125153661872807613603333 42585966311601151427550625)
      ·
        refine ⟨31939474733700863570662969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42585966311601151427550625 31939474733700863570662969)
        ·
          refine ⟨23954606050275647677997227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31939474733700863570662969 23954606050275647677997227)
          ·
            refine ⟨35931909075413471516995841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23954606050275647677997227 35931909075413471516995841)
            ·
              refine ⟨26948931806560103637746881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35931909075413471516995841 26948931806560103637746881)
              ·
                refine ⟨20211698854920077728310161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26948931806560103637746881 20211698854920077728310161)
                ·
                  refine ⟨15158774141190058296232621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20211698854920077728310161 15158774141190058296232621)
                  ·
                    refine ⟨5684540302946271861087233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15158774141190058296232621 5684540302946271861087233)
                    ·
                      refine ⟨4263405227209703895815425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684540302946271861087233 4263405227209703895815425)
                      ·
                        rfl

theorem cell23_8302952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_8302952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302952 prefixEnd_8302952 := by exact prefixLift 8302952
  have htrace : WordTrace (prefixWord ++ tailWord_8302952) baseStart_8302952 baseEnd_8302952 := by
    simpa [prefixWord, tailWord_8302952, baseEnd_8302952] using wordTrace_append hprefix tailTrace_8302952
  have hstable : (prefixWord ++ tailWord_8302952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302952).length < 2 ^ (prefixWord ++ tailWord_8302952).sum := by decide
  have hdescent : baseEnd_8302952 < baseStart_8302952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302965 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_8302965 : Nat := 118140960795 + 8302965 * 2 ^ 59
def prefixEnd_8302965 : Nat := 4983230072969 + 3 ^ 40 * 8302965 * 2
def baseEnd_8302965 : Nat := 4263411902458212344952865

theorem tailTrace_8302965 : CollatzResearch.WordTrace tailWord_8302965 prefixEnd_8302965 4263411902458212344952865 := by
  unfold tailWord_8302965
  simp only [CollatzResearch.WordTrace]
  refine ⟨302834012364783313371694349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201889341576522208914462899 302834012364783313371694349)
  ·
    refine ⟨113562754636793742514385381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302834012364783313371694349 113562754636793742514385381)
    ·
      refine ⟨21293016494398826721447259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113562754636793742514385381 21293016494398826721447259)
      ·
        refine ⟨31939524741598240082170889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21293016494398826721447259 31939524741598240082170889)
        ·
          refine ⟨23954643556198680061628167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31939524741598240082170889 23954643556198680061628167)
          ·
            refine ⟨35931965334298020092442251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23954643556198680061628167 35931965334298020092442251)
            ·
              refine ⟨53897948001447030138663377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35931965334298020092442251 53897948001447030138663377)
              ·
                refine ⟨40423461001085272603997533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53897948001447030138663377 40423461001085272603997533)
                ·
                  refine ⟨15158797875406977226499075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40423461001085272603997533 15158797875406977226499075)
                  ·
                    refine ⟨22738196813110465839748613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15158797875406977226499075 22738196813110465839748613)
                    ·
                      refine ⟨4263411902458212344952865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22738196813110465839748613 4263411902458212344952865)
                      ·
                        rfl

theorem cell23_8302965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_8302965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302965 prefixEnd_8302965 := by exact prefixLift 8302965
  have htrace : WordTrace (prefixWord ++ tailWord_8302965) baseStart_8302965 baseEnd_8302965 := by
    simpa [prefixWord, tailWord_8302965, baseEnd_8302965] using wordTrace_append hprefix tailTrace_8302965
  have hstable : (prefixWord ++ tailWord_8302965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302965).length < 2 ^ (prefixWord ++ tailWord_8302965).sum := by decide
  have hdescent : baseEnd_8302965 < baseStart_8302965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302985 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_8302985 : Nat := 118140960795 + 8302985 * 2 ^ 59
def prefixEnd_8302985 : Nat := 4983230072969 + 3 ^ 40 * 8302985 * 2
def baseEnd_8302985 : Nat := 4263422172071302266702773

theorem tailTrace_8302985 : CollatzResearch.WordTrace tailWord_8302985 prefixEnd_8302985 4263422172071302266702773 := by
  unfold tailWord_8302985
  simp only [CollatzResearch.WordTrace]
  refine ⟨302834741824710856787422409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201889827883140571191614939 302834741824710856787422409)
  ·
    refine ⟨227126056368533142590566807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302834741824710856787422409 227126056368533142590566807)
    ·
      refine ⟨340689084552799713885850211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227126056368533142590566807 340689084552799713885850211)
      ·
        refine ⟨511033626829199570828775317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340689084552799713885850211 511033626829199570828775317)
        ·
          refine ⟨23954701257618729882598843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 511033626829199570828775317 23954701257618729882598843)
          ·
            refine ⟨35932051886428094823898265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23954701257618729882598843 35932051886428094823898265)
            ·
              refine ⟨26949038914821071117923699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35932051886428094823898265 26949038914821071117923699)
              ·
                refine ⟨40423558372231606676885549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26949038914821071117923699 40423558372231606676885549)
                ·
                  refine ⟨15158834389586852503832081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40423558372231606676885549 15158834389586852503832081)
                  ·
                    refine ⟨11369125792190139377874061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15158834389586852503832081 11369125792190139377874061)
                    ·
                      refine ⟨4263422172071302266702773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11369125792190139377874061 4263422172071302266702773)
                      ·
                        rfl

theorem cell23_8302985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_8302985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302985 prefixEnd_8302985 := by exact prefixLift 8302985
  have htrace : WordTrace (prefixWord ++ tailWord_8302985) baseStart_8302985 baseEnd_8302985 := by
    simpa [prefixWord, tailWord_8302985, baseEnd_8302985] using wordTrace_append hprefix tailTrace_8302985
  have hstable : (prefixWord ++ tailWord_8302985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302985).length < 2 ^ (prefixWord ++ tailWord_8302985).sum := by decide
  have hdescent : baseEnd_8302985 < baseStart_8302985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302986 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_8302986 : Nat := 118140960795 + 8302986 * 2 ^ 59
def prefixEnd_8302986 : Nat := 4983230072969 + 3 ^ 40 * 8302986 * 2
def baseEnd_8302986 : Nat := 4263422685551956762790269

theorem tailTrace_8302986 : CollatzResearch.WordTrace tailWord_8302986 prefixEnd_8302986 4263422685551956762790269 := by
  unfold tailWord_8302986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75708694574426808489552203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201889852198471489305472541 75708694574426808489552203)
  ·
    refine ⟨113563041861640212734328305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75708694574426808489552203 113563041861640212734328305)
    ·
      refine ⟨85172281396230159550746229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113563041861640212734328305 85172281396230159550746229)
      ·
        refine ⟨7984901380896577457882459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85172281396230159550746229 7984901380896577457882459)
        ·
          refine ⟨11977352071344866186823689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7984901380896577457882459 11977352071344866186823689)
          ·
            refine ⟨8983014053508649640117767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11977352071344866186823689 8983014053508649640117767)
            ·
              refine ⟨13474521080262974460176651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983014053508649640117767 13474521080262974460176651)
              ·
                refine ⟨20211781620394461690264977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474521080262974460176651 20211781620394461690264977)
                ·
                  refine ⟨15158836215295846267698733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20211781620394461690264977 15158836215295846267698733)
                  ·
                    refine ⟨5684563580735942350387025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15158836215295846267698733 5684563580735942350387025)
                    ·
                      refine ⟨4263422685551956762790269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684563580735942350387025 4263422685551956762790269)
                      ·
                        rfl

theorem cell23_8302986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_8302986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302986 prefixEnd_8302986 := by exact prefixLift 8302986
  have htrace : WordTrace (prefixWord ++ tailWord_8302986) baseStart_8302986 baseEnd_8302986 := by
    simpa [prefixWord, tailWord_8302986, baseEnd_8302986] using wordTrace_append hprefix tailTrace_8302986
  have hstable : (prefixWord ++ tailWord_8302986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302986).length < 2 ^ (prefixWord ++ tailWord_8302986).sum := by decide
  have hdescent : baseEnd_8302986 < baseStart_8302986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302996 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_8302996 : Nat := 118140960795 + 8302996 * 2 ^ 59
def prefixEnd_8302996 : Nat := 4983230072969 + 3 ^ 40 * 8302996 * 2
def baseEnd_8302996 : Nat := 1421142606786167241221741

theorem tailTrace_8302996 : CollatzResearch.WordTrace tailWord_8302996 prefixEnd_8302996 1421142606786167241221741 := by
  unfold tailWord_8302996
  simp only [CollatzResearch.WordTrace]
  refine ⟨151417571513835502833036421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201890095351780670444048561 151417571513835502833036421)
  ·
    refine ⟨28390794658844156781194329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151417571513835502833036421 28390794658844156781194329)
    ·
      refine ⟨21293095994133117585895747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28390794658844156781194329 21293095994133117585895747)
      ·
        refine ⟨31939643991199676378843621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21293095994133117585895747 31939643991199676378843621)
        ·
          refine ⟨5988683248349939321033179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31939643991199676378843621 5988683248349939321033179)
          ·
            refine ⟨8983024872524908981549769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988683248349939321033179 8983024872524908981549769)
            ·
              refine ⟨6737268654393681736162327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8983024872524908981549769 6737268654393681736162327)
              ·
                refine ⟨10105902981590522604243491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6737268654393681736162327 10105902981590522604243491)
                ·
                  refine ⟨15158854472385783906365237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10105902981590522604243491 15158854472385783906365237)
                  ·
                    refine ⟨1421142606786167241221741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15158854472385783906365237 1421142606786167241221741)
                    ·
                      rfl

theorem cell23_8302996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_8302996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302996 prefixEnd_8302996 := by exact prefixLift 8302996
  have htrace : WordTrace (prefixWord ++ tailWord_8302996) baseStart_8302996 baseEnd_8302996 := by
    simpa [prefixWord, tailWord_8302996, baseEnd_8302996] using wordTrace_append hprefix tailTrace_8302996
  have hstable : (prefixWord ++ tailWord_8302996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302996).length < 2 ^ (prefixWord ++ tailWord_8302996).sum := by decide
  have hdescent : baseEnd_8302996 < baseStart_8302996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8302999 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 1, 2, 2]
def baseStart_8302999 : Nat := 118140960795 + 8302999 * 2 ^ 59
def prefixEnd_8302999 : Nat := 4983230072969 + 3 ^ 40 * 8302999 * 2
def baseEnd_8302999 : Nat := 4263429360800465211927709

theorem tailTrace_8302999 : CollatzResearch.WordTrace tailWord_8302999 prefixEnd_8302999 4263429360800465211927709 := by
  unfold tailWord_8302999
  simp only [CollatzResearch.WordTrace]
  refine ⟨302835252446660137178432051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201890168297773424785621367 302835252446660137178432051)
  ·
    refine ⟨454252878669990205767648077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302835252446660137178432051 454252878669990205767648077)
    ·
      refine ⟨170344829501246327162868029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454252878669990205767648077 170344829501246327162868029)
      ·
        refine ⟨63879311062967372686075511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170344829501246327162868029 63879311062967372686075511)
        ·
          refine ⟨95818966594451059029113267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63879311062967372686075511 95818966594451059029113267)
          ·
            refine ⟨143728449891676588543669901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95818966594451059029113267 143728449891676588543669901)
            ·
              refine ⟨53898168709378720703876213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143728449891676588543669901 53898168709378720703876213)
              ·
                refine ⟨5052953316504255065988395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53898168709378720703876213 5052953316504255065988395)
                ·
                  refine ⟨7579429974756382598982593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052953316504255065988395 7579429974756382598982593)
                  ·
                    refine ⟨5684572481067286949236945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579429974756382598982593 5684572481067286949236945)
                    ·
                      refine ⟨4263429360800465211927709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684572481067286949236945 4263429360800465211927709)
                      ·
                        rfl

theorem cell23_8302999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_8302999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8302999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8302999 prefixEnd_8302999 := by exact prefixLift 8302999
  have htrace : WordTrace (prefixWord ++ tailWord_8302999) baseStart_8302999 baseEnd_8302999 := by
    simpa [prefixWord, tailWord_8302999, baseEnd_8302999] using wordTrace_append hprefix tailTrace_8302999
  have hstable : (prefixWord ++ tailWord_8302999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8302999).length < 2 ^ (prefixWord ++ tailWord_8302999).sum := by decide
  have hdescent : baseEnd_8302999 < baseStart_8302999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8302999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303002 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_8303002 : Nat := 118140960795 + 8303002 * 2 ^ 59
def prefixEnd_8303002 : Nat := 4983230072969 + 3 ^ 40 * 8303002 * 2
def baseEnd_8303002 : Nat := 4263430901242428700190195

theorem tailTrace_8303002 : CollatzResearch.WordTrace tailWord_8303002 prefixEnd_8303002 4263430901242428700190195 := by
  unfold tailWord_8303002
  simp only [CollatzResearch.WordTrace]
  refine ⟨75708840466412317172697815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201890241243766179127194173 75708840466412317172697815)
  ·
    refine ⟨113563260699618475759046723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75708840466412317172697815 113563260699618475759046723)
    ·
      refine ⟨170344891049427713638570085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113563260699618475759046723 170344891049427713638570085)
      ·
        refine ⟨31939667071767696307231891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170344891049427713638570085 31939667071767696307231891)
        ·
          refine ⟨47909500607651544460847837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31939667071767696307231891 47909500607651544460847837)
          ·
            refine ⟨17966062727869329172817939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47909500607651544460847837 17966062727869329172817939)
            ·
              refine ⟨26949094091803993759226909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17966062727869329172817939 26949094091803993759226909)
              ·
                refine ⟨10105910284426497659710091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26949094091803993759226909 10105910284426497659710091)
                ·
                  refine ⟨15158865426639746489565137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10105910284426497659710091 15158865426639746489565137)
                  ·
                    refine ⟨11369149069979809867173853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15158865426639746489565137 11369149069979809867173853)
                    ·
                      refine ⟨4263430901242428700190195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11369149069979809867173853 4263430901242428700190195)
                      ·
                        rfl

theorem cell23_8303002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_8303002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303002 prefixEnd_8303002 := by exact prefixLift 8303002
  have htrace : WordTrace (prefixWord ++ tailWord_8303002) baseStart_8303002 baseEnd_8303002 := by
    simpa [prefixWord, tailWord_8303002, baseEnd_8303002] using wordTrace_append hprefix tailTrace_8303002
  have hstable : (prefixWord ++ tailWord_8303002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303002).length < 2 ^ (prefixWord ++ tailWord_8303002).sum := by decide
  have hdescent : baseEnd_8303002 < baseStart_8303002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303016 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_8303016 : Nat := 118140960795 + 8303016 * 2 ^ 59
def prefixEnd_8303016 : Nat := 4983230072969 + 3 ^ 40 * 8303016 * 2
def baseEnd_8303016 : Nat := 4263438089971591645415131

theorem tailTrace_8303016 : CollatzResearch.WordTrace tailWord_8303016 prefixEnd_8303016 4263438089971591645415131 := by
  unfold tailWord_8303016
  simp only [CollatzResearch.WordTrace]
  refine ⟨151417936243799274540900451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201890581658399032721200601 151417936243799274540900451)
  ·
    refine ⟨227126904365698911811350677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151417936243799274540900451 227126904365698911811350677)
    ·
      refine ⟨10646573642142136491157063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227126904365698911811350677 10646573642142136491157063)
      ·
        refine ⟨15969860463213204736735595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10646573642142136491157063 15969860463213204736735595)
        ·
          refine ⟨23954790694819807105103393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15969860463213204736735595 23954790694819807105103393)
          ·
            refine ⟨17966093021114855328827545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23954790694819807105103393 17966093021114855328827545)
            ·
              refine ⟨13474569765836141496620659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17966093021114855328827545 13474569765836141496620659)
              ·
                refine ⟨20211854648754212244930989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474569765836141496620659 20211854648754212244930989)
                ·
                  refine ⟨7579445493282829591849121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20211854648754212244930989 7579445493282829591849121)
                  ·
                    refine ⟨5684584119962122193886841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579445493282829591849121 5684584119962122193886841)
                    ·
                      refine ⟨4263438089971591645415131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684584119962122193886841 4263438089971591645415131)
                      ·
                        rfl

theorem cell23_8303016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_8303016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303016 prefixEnd_8303016 := by exact prefixLift 8303016
  have htrace : WordTrace (prefixWord ++ tailWord_8303016) baseStart_8303016 baseEnd_8303016 := by
    simpa [prefixWord, tailWord_8303016, baseEnd_8303016] using wordTrace_append hprefix tailTrace_8303016
  have hstable : (prefixWord ++ tailWord_8303016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303016).length < 2 ^ (prefixWord ++ tailWord_8303016).sum := by decide
  have hdescent : baseEnd_8303016 < baseStart_8303016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303029 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_8303029 : Nat := 118140960795 + 8303029 * 2 ^ 59
def prefixEnd_8303029 : Nat := 4983230072969 + 3 ^ 40 * 8303029 * 2
def baseEnd_8303029 : Nat := 4263444765220100094552571

theorem tailTrace_8303029 : CollatzResearch.WordTrace tailWord_8303029 prefixEnd_8303029 4263444765220100094552571 := by
  unfold tailWord_8303029
  simp only [CollatzResearch.WordTrace]
  refine ⟨302836346636551452302024141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201890897757700968201349427 302836346636551452302024141)
  ·
    refine ⟨113563629988706794613259053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302836346636551452302024141 113563629988706794613259053)
    ·
      refine ⟨42586361245765047979972145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113563629988706794613259053 42586361245765047979972145)
      ·
        refine ⟨31939770934323785984979109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42586361245765047979972145 31939770934323785984979109)
        ·
          refine ⟨5988707050185709872183583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31939770934323785984979109 5988707050185709872183583)
          ·
            refine ⟨8983060575278564808275375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988707050185709872183583 8983060575278564808275375)
            ·
              refine ⟨13474590862917847212413063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983060575278564808275375 13474590862917847212413063)
              ·
                refine ⟨20211886294376770818619595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474590862917847212413063 20211886294376770818619595)
                ·
                  refine ⟨30317829441565156227929393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20211886294376770818619595 30317829441565156227929393)
                  ·
                    refine ⟨22738372081173867170947045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30317829441565156227929393 22738372081173867170947045)
                    ·
                      refine ⟨4263444765220100094552571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22738372081173867170947045 4263444765220100094552571)
                      ·
                        rfl

theorem cell23_8303029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_8303029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303029 prefixEnd_8303029 := by exact prefixLift 8303029
  have htrace : WordTrace (prefixWord ++ tailWord_8303029) baseStart_8303029 baseEnd_8303029 := by
    simpa [prefixWord, tailWord_8303029, baseEnd_8303029] using wordTrace_append hprefix tailTrace_8303029
  have hstable : (prefixWord ++ tailWord_8303029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303029).length < 2 ^ (prefixWord ++ tailWord_8303029).sum := by decide
  have hdescent : baseEnd_8303029 < baseStart_8303029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303055 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 3, 4, 2]
def baseStart_8303055 : Nat := 118140960795 + 8303055 * 2 ^ 59
def prefixEnd_8303055 : Nat := 4983230072969 + 3 ^ 40 * 8303055 * 2
def baseEnd_8303055 : Nat := 4263458115717116992827451

theorem tailTrace_8303055 : CollatzResearch.WordTrace tailWord_8303055 prefixEnd_8303055 4263458115717116992827451 := by
  unfold tailWord_8303055
  simp only [CollatzResearch.WordTrace]
  refine ⟨302837294934457258742470619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201891529956304839161647079 302837294934457258742470619)
  ·
    refine ⟨454255942401685888113705929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302837294934457258742470619 454255942401685888113705929)
    ·
      refine ⟨340691956801264416085279447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454255942401685888113705929 340691956801264416085279447)
      ·
        refine ⟨511037935201896624127919171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340691956801264416085279447 511037935201896624127919171)
        ·
          refine ⟨766556902802844936191878757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511037935201896624127919171 766556902802844936191878757)
          ·
            refine ⟨143729419275533425535977267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 766556902802844936191878757 143729419275533425535977267)
            ·
              refine ⟨215594128913300138303965901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143729419275533425535977267 215594128913300138303965901)
              ·
                refine ⟨80847798342487551863987213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215594128913300138303965901 80847798342487551863987213)
                ·
                  refine ⟨30317924378432831948995205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80847798342487551863987213 30317924378432831948995205)
                  ·
                    refine ⟨5684610820956155990436601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30317924378432831948995205 5684610820956155990436601)
                    ·
                      refine ⟨4263458115717116992827451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684610820956155990436601 4263458115717116992827451)
                      ·
                        rfl

theorem cell23_8303055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 4, 2].length) (baseStart_8303055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303055 prefixEnd_8303055 := by exact prefixLift 8303055
  have htrace : WordTrace (prefixWord ++ tailWord_8303055) baseStart_8303055 baseEnd_8303055 := by
    simpa [prefixWord, tailWord_8303055, baseEnd_8303055] using wordTrace_append hprefix tailTrace_8303055
  have hstable : (prefixWord ++ tailWord_8303055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303055).length < 2 ^ (prefixWord ++ tailWord_8303055).sum := by decide
  have hdescent : baseEnd_8303055 < baseStart_8303055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303072 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2]
def baseStart_8303072 : Nat := 118140960795 + 8303072 * 2 ^ 59
def prefixEnd_8303072 : Nat := 4983230072969 + 3 ^ 40 * 8303072 * 2
def baseEnd_8303072 : Nat := 4263466844888243426314873

theorem tailTrace_8303072 : CollatzResearch.WordTrace tailWord_8303072 prefixEnd_8303072 4263466844888243426314873 := by
  unfold tailWord_8303072
  simp only [CollatzResearch.WordTrace]
  refine ⟨151418957487697835322919735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201891943316930447097226313 151418957487697835322919735)
  ·
    refine ⟨227128436231546752984379603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151418957487697835322919735 227128436231546752984379603)
    ·
      refine ⟨340692654347320129476569405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227128436231546752984379603 340692654347320129476569405)
      ·
        refine ⟨127759745380245048553713527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340692654347320129476569405 127759745380245048553713527)
        ·
          refine ⟨191639618070367572830570291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127759745380245048553713527 191639618070367572830570291)
          ·
            refine ⟨287459427105551359245855437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191639618070367572830570291 287459427105551359245855437)
            ·
              refine ⟨107797285164581759717195789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287459427105551359245855437 107797285164581759717195789)
              ·
                refine ⟨40423981936718159893948421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107797285164581759717195789 40423981936718159893948421)
                ·
                  refine ⟨7579496613134654980115329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40423981936718159893948421 7579496613134654980115329)
                  ·
                    refine ⟨5684622459850991235086497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579496613134654980115329 5684622459850991235086497)
                    ·
                      refine ⟨4263466844888243426314873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684622459850991235086497 4263466844888243426314873)
                      ·
                        rfl

theorem cell23_8303072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_8303072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303072 prefixEnd_8303072 := by exact prefixLift 8303072
  have htrace : WordTrace (prefixWord ++ tailWord_8303072) baseStart_8303072 baseEnd_8303072 := by
    simpa [prefixWord, tailWord_8303072, baseEnd_8303072] using wordTrace_append hprefix tailTrace_8303072
  have hstable : (prefixWord ++ tailWord_8303072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303072).length < 2 ^ (prefixWord ++ tailWord_8303072).sum := by decide
  have hdescent : baseEnd_8303072 < baseStart_8303072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303089 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_8303089 : Nat := 118140960795 + 8303089 * 2 ^ 59
def prefixEnd_8303089 : Nat := 4983230072969 + 3 ^ 40 * 8303089 * 2
def baseEnd_8303089 : Nat := 4263475574059369859802295

theorem tailTrace_8303089 : CollatzResearch.WordTrace tailWord_8303089 prefixEnd_8303089 4263475574059369859802295 := by
  unfold tailWord_8303089
  simp only [CollatzResearch.WordTrace]
  refine ⟨302838535016334082549208321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201892356677556055032805547 302838535016334082549208321)
  ·
    refine ⟨227128901262250561911906241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302838535016334082549208321 227128901262250561911906241)
    ·
      refine ⟨170346675946687921433929681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227128901262250561911906241 170346675946687921433929681)
      ·
        refine ⟨127760006960015941075447261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170346675946687921433929681 127760006960015941075447261)
        ·
          refine ⟨47910002610005977903292723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127760006960015941075447261 47910002610005977903292723)
          ·
            refine ⟨71865003915008966854939085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47910002610005977903292723 71865003915008966854939085)
            ·
              refine ⟨26949376468128362570602157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71865003915008966854939085 26949376468128362570602157)
              ·
                refine ⟨10106016175548135963975809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26949376468128362570602157 10106016175548135963975809)
                ·
                  refine ⟨7579512131661101972981857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10106016175548135963975809 7579512131661101972981857)
                  ·
                    refine ⟨5684634098745826479736393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579512131661101972981857 5684634098745826479736393)
                    ·
                      refine ⟨4263475574059369859802295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684634098745826479736393 4263475574059369859802295)
                      ·
                        rfl

theorem cell23_8303089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_8303089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303089 prefixEnd_8303089 := by exact prefixLift 8303089
  have htrace : WordTrace (prefixWord ++ tailWord_8303089) baseStart_8303089 baseEnd_8303089 := by
    simpa [prefixWord, tailWord_8303089, baseEnd_8303089] using wordTrace_append hprefix tailTrace_8303089
  have hstable : (prefixWord ++ tailWord_8303089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303089).length < 2 ^ (prefixWord ++ tailWord_8303089).sum := by decide
  have hdescent : baseEnd_8303089 < baseStart_8303089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303093 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_8303093 : Nat := 118140960795 + 8303093 * 2 ^ 59
def prefixEnd_8303093 : Nat := 4983230072969 + 3 ^ 40 * 8303093 * 2
def baseEnd_8303093 : Nat := 4263477627981987844152277

theorem tailTrace_8303093 : CollatzResearch.WordTrace tailWord_8303093 prefixEnd_8303093 4263477627981987844152277 := by
  unfold tailWord_8303093
  simp only [CollatzResearch.WordTrace]
  refine ⟨302838680908319591232353933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201892453938879727488235955 302838680908319591232353933)
  ·
    refine ⟨113564505340619846712132725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302838680908319591232353933 113564505340619846712132725)
    ·
      refine ⟨10646672375683110629262443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113564505340619846712132725 10646672375683110629262443)
      ·
        refine ⟨15970008563524665943893665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10646672375683110629262443 15970008563524665943893665)
        ·
          refine ⟨11977506422643499457920249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15970008563524665943893665 11977506422643499457920249)
          ·
            refine ⟨8983129816982624593440187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11977506422643499457920249 8983129816982624593440187)
            ·
              refine ⟨13474694725473936890160281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983129816982624593440187 13474694725473936890160281)
              ·
                refine ⟨10106021044105452667620211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13474694725473936890160281 10106021044105452667620211)
                ·
                  refine ⟨15159031566158179001430317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10106021044105452667620211 15159031566158179001430317)
                  ·
                    refine ⟨5684636837309317125536369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15159031566158179001430317 5684636837309317125536369)
                    ·
                      refine ⟨4263477627981987844152277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684636837309317125536369 4263477627981987844152277)
                      ·
                        rfl

theorem cell23_8303093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_8303093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303093 prefixEnd_8303093 := by exact prefixLift 8303093
  have htrace : WordTrace (prefixWord ++ tailWord_8303093) baseStart_8303093 baseEnd_8303093 := by
    simpa [prefixWord, tailWord_8303093, baseEnd_8303093] using wordTrace_append hprefix tailTrace_8303093
  have hstable : (prefixWord ++ tailWord_8303093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303093).length < 2 ^ (prefixWord ++ tailWord_8303093).sum := by decide
  have hdescent : baseEnd_8303093 < baseStart_8303093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303106 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_8303106 : Nat := 118140960795 + 8303106 * 2 ^ 59
def prefixEnd_8303106 : Nat := 4983230072969 + 3 ^ 40 * 8303106 * 2
def baseEnd_8303106 : Nat := 4263484303230496293289717

theorem tailTrace_8303106 : CollatzResearch.WordTrace tailWord_8303106 prefixEnd_8303106 4263484303230496293289717 := by
  unfold tailWord_8303106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75709788764318123613144293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201892770038181662968384781 75709788764318123613144293)
  ·
    refine ⟨14195585393309648177464555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75709788764318123613144293 14195585393309648177464555)
    ·
      refine ⟨21293378089964472266196833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14195585393309648177464555 21293378089964472266196833)
      ·
        refine ⟨15970033567473354199647625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21293378089964472266196833 15970033567473354199647625)
        ·
          refine ⟨11977525175605015649735719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15970033567473354199647625 11977525175605015649735719)
          ·
            refine ⟨17966287763407523474603579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11977525175605015649735719 17966287763407523474603579)
            ·
              refine ⟨26949431645111285211905369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17966287763407523474603579 26949431645111285211905369)
              ·
                refine ⟨20212073733833463908929027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26949431645111285211905369 20212073733833463908929027)
                ·
                  refine ⟨30318110600750195863393541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20212073733833463908929027 30318110600750195863393541)
                  ·
                    refine ⟨5684645737640661724386289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30318110600750195863393541 5684645737640661724386289)
                    ·
                      refine ⟨4263484303230496293289717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684645737640661724386289 4263484303230496293289717)
                      ·
                        rfl

theorem cell23_8303106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_8303106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303106 prefixEnd_8303106 := by exact prefixLift 8303106
  have htrace : WordTrace (prefixWord ++ tailWord_8303106) baseStart_8303106 baseEnd_8303106 := by
    simpa [prefixWord, tailWord_8303106, baseEnd_8303106] using wordTrace_append hprefix tailTrace_8303106
  have hstable : (prefixWord ++ tailWord_8303106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303106).length < 2 ^ (prefixWord ++ tailWord_8303106).sum := by decide
  have hdescent : baseEnd_8303106 < baseStart_8303106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303125 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_8303125 : Nat := 118140960795 + 8303125 * 2 ^ 59
def prefixEnd_8303125 : Nat := 4983230072969 + 3 ^ 40 * 8303125 * 2
def baseEnd_8303125 : Nat := 1421164686454310572984043

theorem tailTrace_8303125 : CollatzResearch.WordTrace tailWord_8303125 prefixEnd_8303125 1421164686454310572984043 := by
  unfold tailWord_8303125
  simp only [CollatzResearch.WordTrace]
  refine ⟨302839848044203660697518829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201893232029469107131679219 302839848044203660697518829)
  ·
    refine ⟨113564943016576372761569561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302839848044203660697518829 113564943016576372761569561)
    ·
      refine ⟨85173707262432279571177171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113564943016576372761569561 85173707262432279571177171)
      ·
        refine ⟨127760560893648419356765757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85173707262432279571177171 127760560893648419356765757)
        ·
          refine ⟨47910210335118157258787159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127760560893648419356765757 47910210335118157258787159)
          ·
            refine ⟨71865315502677235888180739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47910210335118157258787159 71865315502677235888180739)
            ·
              refine ⟨107797973254015853832271109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71865315502677235888180739 107797973254015853832271109)
              ·
                refine ⟨20212119985127972593550833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107797973254015853832271109 20212119985127972593550833)
                ·
                  refine ⟨15159089988845979445163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20212119985127972593550833 15159089988845979445163125)
                  ·
                    refine ⟨1421164686454310572984043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15159089988845979445163125 1421164686454310572984043)
                    ·
                      rfl

theorem cell23_8303125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_8303125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303125 prefixEnd_8303125 := by exact prefixLift 8303125
  have htrace : WordTrace (prefixWord ++ tailWord_8303125) baseStart_8303125 baseEnd_8303125 := by
    simpa [prefixWord, tailWord_8303125, baseEnd_8303125] using wordTrace_append hprefix tailTrace_8303125
  have hstable : (prefixWord ++ tailWord_8303125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303125).length < 2 ^ (prefixWord ++ tailWord_8303125).sum := by decide
  have hdescent : baseEnd_8303125 < baseStart_8303125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303132 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_8303132 : Nat := 118140960795 + 8303132 * 2 ^ 59
def prefixEnd_8303132 : Nat := 4983230072969 + 3 ^ 40 * 8303132 * 2
def baseEnd_8303132 : Nat := 4263497653727513191564597

theorem tailTrace_8303132 : CollatzResearch.WordTrace tailWord_8303132 prefixEnd_8303132 4263497653727513191564597 := by
  unfold tailWord_8303132
  simp only [CollatzResearch.WordTrace]
  refine ⟨151420051677589150446511825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201893402236785533928682433 151420051677589150446511825)
  ·
    refine ⟨113565038758191862834883869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151420051677589150446511825 113565038758191862834883869)
    ·
      refine ⟨42586889534321948563081451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113565038758191862834883869 42586889534321948563081451)
      ·
        refine ⟨63880334301482922844622177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42586889534321948563081451 63880334301482922844622177)
        ·
          refine ⟨47910250726112192133466633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63880334301482922844622177 47910250726112192133466633)
          ·
            refine ⟨35932688044584144100099975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47910250726112192133466633 35932688044584144100099975)
            ·
              refine ⟨53899032066876216150149963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35932688044584144100099975 53899032066876216150149963)
              ·
                refine ⟨80848548100314324225224945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53899032066876216150149963 80848548100314324225224945)
                ·
                  refine ⟨60636411075235743168918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80848548100314324225224945 60636411075235743168918709)
                  ·
                    refine ⟨5684663538303350922086129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60636411075235743168918709 5684663538303350922086129)
                    ·
                      refine ⟨4263497653727513191564597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684663538303350922086129 4263497653727513191564597)
                      ·
                        rfl

theorem cell23_8303132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_8303132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303132 prefixEnd_8303132 := by exact prefixLift 8303132
  have htrace : WordTrace (prefixWord ++ tailWord_8303132) baseStart_8303132 baseEnd_8303132 := by
    simpa [prefixWord, tailWord_8303132, baseEnd_8303132] using wordTrace_append hprefix tailTrace_8303132
  have hstable : (prefixWord ++ tailWord_8303132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303132).length < 2 ^ (prefixWord ++ tailWord_8303132).sum := by decide
  have hdescent : baseEnd_8303132 < baseStart_8303132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303162 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_8303162 : Nat := 118140960795 + 8303162 * 2 ^ 59
def prefixEnd_8303162 : Nat := 4983230072969 + 3 ^ 40 * 8303162 * 2
def baseEnd_8303162 : Nat := 4263513058147148074189459

theorem tailTrace_8303162 : CollatzResearch.WordTrace tailWord_8303162 prefixEnd_8303162 4263513058147148074189459 := by
  unfold tailWord_8303162
  simp only [CollatzResearch.WordTrace]
  refine ⟨75710299386267404004153935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201894131696713077344410493 75710299386267404004153935)
  ·
    refine ⟨113565449079401106006230903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75710299386267404004153935 113565449079401106006230903)
    ·
      refine ⟨170348173619101659009346355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113565449079401106006230903 170348173619101659009346355)
      ·
        refine ⟨255522260428652488514019533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170348173619101659009346355 255522260428652488514019533)
        ·
          refine ⟨95820847660744683192757325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255522260428652488514019533 95820847660744683192757325)
          ·
            refine ⟨35932817872779256197283997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95820847660744683192757325 35932817872779256197283997)
            ·
              refine ⟨13474806702292221073981499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35932817872779256197283997 13474806702292221073981499)
              ·
                refine ⟨20212210053438331610972249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13474806702292221073981499 20212210053438331610972249)
                ·
                  refine ⟨15159157540078748708229187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20212210053438331610972249 15159157540078748708229187)
                  ·
                    refine ⟨22738736310118123062343781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15159157540078748708229187 22738736310118123062343781)
                    ·
                      refine ⟨4263513058147148074189459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22738736310118123062343781 4263513058147148074189459)
                      ·
                        rfl

theorem cell23_8303162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_8303162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303162 prefixEnd_8303162 := by exact prefixLift 8303162
  have htrace : WordTrace (prefixWord ++ tailWord_8303162) baseStart_8303162 baseEnd_8303162 := by
    simpa [prefixWord, tailWord_8303162, baseEnd_8303162] using wordTrace_append hprefix tailTrace_8303162
  have hstable : (prefixWord ++ tailWord_8303162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303162).length < 2 ^ (prefixWord ++ tailWord_8303162).sum := by decide
  have hdescent : baseEnd_8303162 < baseStart_8303162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303175 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_8303175 : Nat := 118140960795 + 8303175 * 2 ^ 59
def prefixEnd_8303175 : Nat := 4983230072969 + 3 ^ 40 * 8303175 * 2
def baseEnd_8303175 : Nat := 4263519733395656523326899

theorem tailTrace_8303175 : CollatzResearch.WordTrace tailWord_8303175 prefixEnd_8303175 4263519733395656523326899 := by
  unfold tailWord_8303175
  simp only [CollatzResearch.WordTrace]
  refine ⟨302841671694022519236838979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201894447796015012824559319 302841671694022519236838979)
  ·
    refine ⟨454262507541033778855258469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302841671694022519236838979 454262507541033778855258469)
    ·
      refine ⟨85174220163943833535360963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454262507541033778855258469 85174220163943833535360963)
      ·
        refine ⟨127761330245915750303041445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85174220163943833535360963 127761330245915750303041445)
        ·
          refine ⟨23955249421109203181820271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127761330245915750303041445 23955249421109203181820271)
          ·
            refine ⟨35932874131663804772730407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23955249421109203181820271 35932874131663804772730407)
            ·
              refine ⟨53899311197495707159095611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35932874131663804772730407 53899311197495707159095611)
              ·
                refine ⟨80848966796243560738643417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53899311197495707159095611 80848966796243560738643417)
                ·
                  refine ⟨60636725097182670553982563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80848966796243560738643417 60636725097182670553982563)
                  ·
                    refine ⟨90955087645774005830973845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60636725097182670553982563 90955087645774005830973845)
                    ·
                      refine ⟨4263519733395656523326899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90955087645774005830973845 4263519733395656523326899)
                      ·
                        rfl

theorem cell23_8303175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_8303175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303175 prefixEnd_8303175 := by exact prefixLift 8303175
  have htrace : WordTrace (prefixWord ++ tailWord_8303175) baseStart_8303175 baseEnd_8303175 := by
    simpa [prefixWord, tailWord_8303175, baseEnd_8303175] using wordTrace_append hprefix tailTrace_8303175
  have hstable : (prefixWord ++ tailWord_8303175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303175).length < 2 ^ (prefixWord ++ tailWord_8303175).sum := by decide
  have hdescent : baseEnd_8303175 < baseStart_8303175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303182 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_8303182 : Nat := 118140960795 + 8303182 * 2 ^ 59
def prefixEnd_8303182 : Nat := 4983230072969 + 3 ^ 40 * 8303182 * 2
def baseEnd_8303182 : Nat := 4263523327760237995939367

theorem tailTrace_8303182 : CollatzResearch.WordTrace tailWord_8303182 prefixEnd_8303182 4263523327760237995939367 := by
  unfold tailWord_8303182
  simp only [CollatzResearch.WordTrace]
  refine ⟨37855240875624644929042975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201894618003331439621562533 37855240875624644929042975)
  ·
    refine ⟨56782861313436967393564463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37855240875624644929042975 56782861313436967393564463)
    ·
      refine ⟨85174291970155451090346695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56782861313436967393564463 85174291970155451090346695)
      ·
        refine ⟨127761437955233176635520043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85174291970155451090346695 127761437955233176635520043)
        ·
          refine ⟨191642156932849764953280065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127761437955233176635520043 191642156932849764953280065)
          ·
            refine ⟨143731617699637323714960049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191642156932849764953280065 143731617699637323714960049)
            ·
              refine ⟨107798713274727992786220037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143731617699637323714960049 107798713274727992786220037)
              ·
                refine ⟨20212258739011498647416257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107798713274727992786220037 20212258739011498647416257)
                ·
                  refine ⟨15159194054258623985562193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20212258739011498647416257 15159194054258623985562193)
                  ·
                    refine ⟨11369395540693967989171645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15159194054258623985562193 11369395540693967989171645)
                    ·
                      refine ⟨4263523327760237995939367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11369395540693967989171645 4263523327760237995939367)
                      ·
                        rfl

theorem cell23_8303182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_8303182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303182 prefixEnd_8303182 := by exact prefixLift 8303182
  have htrace : WordTrace (prefixWord ++ tailWord_8303182) baseStart_8303182 baseEnd_8303182 := by
    simpa [prefixWord, tailWord_8303182, baseEnd_8303182] using wordTrace_append hprefix tailTrace_8303182
  have hstable : (prefixWord ++ tailWord_8303182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303182).length < 2 ^ (prefixWord ++ tailWord_8303182).sum := by decide
  have hdescent : baseEnd_8303182 < baseStart_8303182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303185 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 8]
def baseStart_8303185 : Nat := 118140960795 + 8303185 * 2 ^ 59
def prefixEnd_8303185 : Nat := 4983230072969 + 3 ^ 40 * 8303185 * 2
def baseEnd_8303185 : Nat := 473724985355800164911317

theorem tailTrace_8303185 : CollatzResearch.WordTrace tailWord_8303185 prefixEnd_8303185 473724985355800164911317 := by
  unfold tailWord_8303185
  simp only [CollatzResearch.WordTrace]
  refine ⟨302842036423986290944703009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201894690949324193963135339 302842036423986290944703009)
  ·
    refine ⟨227131527317989718208527257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302842036423986290944703009 227131527317989718208527257)
    ·
      refine ⟨170348645488492288656395443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227131527317989718208527257 170348645488492288656395443)
      ·
        refine ⟨255522968232738432984593165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170348645488492288656395443 255522968232738432984593165)
        ·
          refine ⟨95821113087276912369222437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255522968232738432984593165 95821113087276912369222437)
          ·
            refine ⟨17966458703864421069229207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95821113087276912369222437 17966458703864421069229207)
            ·
              refine ⟨26949688055796631603843811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17966458703864421069229207 26949688055796631603843811)
              ·
                refine ⟨40424532083694947405765717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26949688055796631603843811 40424532083694947405765717)
                ·
                  refine ⟨473724985355800164911317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40424532083694947405765717 473724985355800164911317)
                  ·
                    rfl

theorem cell23_8303185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_8303185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303185 prefixEnd_8303185 := by exact prefixLift 8303185
  have htrace : WordTrace (prefixWord ++ tailWord_8303185) baseStart_8303185 baseEnd_8303185 := by
    simpa [prefixWord, tailWord_8303185, baseEnd_8303185] using wordTrace_append hprefix tailTrace_8303185
  have hstable : (prefixWord ++ tailWord_8303185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303185).length < 2 ^ (prefixWord ++ tailWord_8303185).sum := by decide
  have hdescent : baseEnd_8303185 < baseStart_8303185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303189 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_8303189 : Nat := 118140960795 + 8303189 * 2 ^ 59
def prefixEnd_8303189 : Nat := 4983230072969 + 3 ^ 40 * 8303189 * 2
def baseEnd_8303189 : Nat := 1421175640708273156183945

theorem tailTrace_8303189 : CollatzResearch.WordTrace tailWord_8303189 prefixEnd_8303189 1421175640708273156183945 := by
  unfold tailWord_8303189
  simp only [CollatzResearch.WordTrace]
  refine ⟨302842182315971799627848621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201894788210647866418565747 302842182315971799627848621)
  ·
    refine ⟨113565818368489424860443233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302842182315971799627848621 113565818368489424860443233)
    ·
      refine ⟨85174363776367068645332425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113565818368489424860443233 85174363776367068645332425)
      ·
        refine ⟨63880772832275301483999319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85174363776367068645332425 63880772832275301483999319)
        ·
          refine ⟨95821159248412952225998979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63880772832275301483999319 95821159248412952225998979)
          ·
            refine ⟨143731738872619428338998469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95821159248412952225998979 143731738872619428338998469)
            ·
              refine ⟨26949701038616142813562213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143731738872619428338998469 26949701038616142813562213)
              ·
                refine ⟨5053068944740526777542915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26949701038616142813562213 5053068944740526777542915)
                ·
                  refine ⟨7579603417110790166314373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053068944740526777542915 7579603417110790166314373)
                  ·
                    refine ⟨1421175640708273156183945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579603417110790166314373 1421175640708273156183945)
                    ·
                      rfl

theorem cell23_8303189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_8303189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303189 prefixEnd_8303189 := by exact prefixLift 8303189
  have htrace : WordTrace (prefixWord ++ tailWord_8303189) baseStart_8303189 baseEnd_8303189 := by
    simpa [prefixWord, tailWord_8303189, baseEnd_8303189] using wordTrace_append hprefix tailTrace_8303189
  have hstable : (prefixWord ++ tailWord_8303189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303189).length < 2 ^ (prefixWord ++ tailWord_8303189).sum := by decide
  have hdescent : baseEnd_8303189 < baseStart_8303189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303215 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 3, 5]
def baseStart_8303215 : Nat := 118140960795 + 8303215 * 2 ^ 59
def prefixEnd_8303215 : Nat := 4983230072969 + 3 ^ 40 * 8303215 * 2
def baseEnd_8303215 : Nat := 1421180090873945455608905

theorem tailTrace_8303215 : CollatzResearch.WordTrace tailWord_8303215 prefixEnd_8303215 1421180090873945455608905 := by
  unfold tailWord_8303215
  simp only [CollatzResearch.WordTrace]
  refine ⟨302843130613877606068295099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201895420409251737378863399 302843130613877606068295099)
  ·
    refine ⟨454264695920816409102442649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302843130613877606068295099 454264695920816409102442649)
    ·
      refine ⟨340698521940612306826831987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454264695920816409102442649 340698521940612306826831987)
      ·
        refine ⟨511047782910918460240247981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340698521940612306826831987 511047782910918460240247981)
        ·
          refine ⟨191642918591594422590092993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511047782910918460240247981 191642918591594422590092993)
          ·
            refine ⟨143732188943695816942569745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191642918591594422590092993 143732188943695816942569745)
            ·
              refine ⟨107799141707771862706927309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143732188943695816942569745 107799141707771862706927309)
              ·
                refine ⟨40424678140414448515097741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107799141707771862706927309 40424678140414448515097741)
                ·
                  refine ⟨15159254302655418193161653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40424678140414448515097741 15159254302655418193161653)
                  ·
                    refine ⟨1421180090873945455608905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15159254302655418193161653 1421180090873945455608905)
                    ·
                      rfl

theorem cell23_8303215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_8303215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303215 prefixEnd_8303215 := by exact prefixLift 8303215
  have htrace : WordTrace (prefixWord ++ tailWord_8303215) baseStart_8303215 baseEnd_8303215 := by
    simpa [prefixWord, tailWord_8303215, baseEnd_8303215] using wordTrace_append hprefix tailTrace_8303215
  have hstable : (prefixWord ++ tailWord_8303215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303215).length < 2 ^ (prefixWord ++ tailWord_8303215).sum := by decide
  have hdescent : baseEnd_8303215 < baseStart_8303215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303232 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_8303232 : Nat := 118140960795 + 8303232 * 2 ^ 59
def prefixEnd_8303232 : Nat := 4983230072969 + 3 ^ 40 * 8303232 * 2
def baseEnd_8303232 : Nat := 1421183000597654266771379

theorem tailTrace_8303232 : CollatzResearch.WordTrace tailWord_8303232 prefixEnd_8303232 1421183000597654266771379 := by
  unfold tailWord_8303232
  simp only [CollatzResearch.WordTrace]
  refine ⟨151421875327408008985831975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201895833769877345314442633 151421875327408008985831975)
  ·
    refine ⟨227132812991112013478747963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151421875327408008985831975 227132812991112013478747963)
    ·
      refine ⟨340699219486668020218121945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227132812991112013478747963 340699219486668020218121945)
      ·
        refine ⟨255524414615001015163591459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340699219486668020218121945 255524414615001015163591459)
        ·
          refine ⟨383286621922501522745387189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255524414615001015163591459 383286621922501522745387189)
          ·
            refine ⟨35933120805234517757380049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383286621922501522745387189 35933120805234517757380049)
            ·
              refine ⟨26949840603925888318035037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35933120805234517757380049 26949840603925888318035037)
              ·
                refine ⟨10106190226472208119263139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26949840603925888318035037 10106190226472208119263139)
                ·
                  refine ⟨15159285339708312178894709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10106190226472208119263139 15159285339708312178894709)
                  ·
                    refine ⟨1421183000597654266771379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15159285339708312178894709 1421183000597654266771379)
                    ·
                      rfl

theorem cell23_8303232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_8303232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303232 prefixEnd_8303232 := by exact prefixLift 8303232
  have htrace : WordTrace (prefixWord ++ tailWord_8303232) baseStart_8303232 baseEnd_8303232 := by
    simpa [prefixWord, tailWord_8303232, baseEnd_8303232] using wordTrace_append hprefix tailTrace_8303232
  have hstable : (prefixWord ++ tailWord_8303232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303232).length < 2 ^ (prefixWord ++ tailWord_8303232).sum := by decide
  have hdescent : baseEnd_8303232 < baseStart_8303232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303239 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_8303239 : Nat := 118140960795 + 8303239 * 2 ^ 59
def prefixEnd_8303239 : Nat := 4983230072969 + 3 ^ 40 * 8303239 * 2
def baseEnd_8303239 : Nat := 4263552596157544272926605

theorem tailTrace_8303239 : CollatzResearch.WordTrace tailWord_8303239 prefixEnd_8303239 4263552596157544272926605 := by
  unfold tailWord_8303239
  simp only [CollatzResearch.WordTrace]
  refine ⟨302844005965790658167168771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201896003977193772111445847 302844005965790658167168771)
  ·
    refine ⟨454266008948685987250753157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302844005965790658167168771 454266008948685987250753157)
    ·
      refine ⟨85174876677878622609516217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454266008948685987250753157 85174876677878622609516217)
      ·
        refine ⟨63881157508408966957137163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85174876677878622609516217 63881157508408966957137163)
        ·
          refine ⟨95821736262613450435705745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63881157508408966957137163 95821736262613450435705745)
          ·
            refine ⟨71866302196960087826779309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95821736262613450435705745 71866302196960087826779309)
            ·
              refine ⟨26949863323860032935042241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71866302196960087826779309 26949863323860032935042241)
              ·
                refine ⟨20212397492895024701281681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26949863323860032935042241 20212397492895024701281681)
                ·
                  refine ⟨15159298119671268525961261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20212397492895024701281681 15159298119671268525961261)
                  ·
                    refine ⟨5684736794876725697235473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15159298119671268525961261 5684736794876725697235473)
                    ·
                      refine ⟨4263552596157544272926605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684736794876725697235473 4263552596157544272926605)
                      ·
                        rfl

theorem cell23_8303239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_8303239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303239 prefixEnd_8303239 := by exact prefixLift 8303239
  have htrace : WordTrace (prefixWord ++ tailWord_8303239) baseStart_8303239 baseEnd_8303239 := by
    simpa [prefixWord, tailWord_8303239, baseEnd_8303239] using wordTrace_append hprefix tailTrace_8303239
  have hstable : (prefixWord ++ tailWord_8303239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303239).length < 2 ^ (prefixWord ++ tailWord_8303239).sum := by decide
  have hdescent : baseEnd_8303239 < baseStart_8303239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303269 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 5, 2, 2]
def baseStart_8303269 : Nat := 118140960795 + 8303269 * 2 ^ 59
def prefixEnd_8303269 : Nat := 4983230072969 + 3 ^ 40 * 8303269 * 2
def baseEnd_8303269 : Nat := 4263568000577179155551467

theorem tailTrace_8303269 : CollatzResearch.WordTrace tailWord_8303269 prefixEnd_8303269 4263568000577179155551467 := by
  unfold tailWord_8303269
  simp only [CollatzResearch.WordTrace]
  refine ⟨302845100155681973290760861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201896733437121315527173907 302845100155681973290760861)
  ·
    refine ⟨113566912558380739984035323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302845100155681973290760861 113566912558380739984035323)
    ·
      refine ⟨170350368837571109976052985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113566912558380739984035323 170350368837571109976052985)
      ·
        refine ⟨127762776628178332482039739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170350368837571109976052985 127762776628178332482039739)
        ·
          refine ⟨191644164942267498723059609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127762776628178332482039739 191644164942267498723059609)
          ·
            refine ⟨143733123706700624042294707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191644164942267498723059609 143733123706700624042294707)
            ·
              refine ⟨215599685560050936063442061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143733123706700624042294707 215599685560050936063442061)
              ·
                refine ⟨80849882085019101023790773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215599685560050936063442061 80849882085019101023790773)
                ·
                  refine ⟨7579676445470540720980385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80849882085019101023790773 7579676445470540720980385)
                  ·
                    refine ⟨5684757334102905540735289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7579676445470540720980385 5684757334102905540735289)
                    ·
                      refine ⟨4263568000577179155551467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5684757334102905540735289 4263568000577179155551467)
                      ·
                        rfl

theorem cell23_8303269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_8303269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303269 prefixEnd_8303269 := by exact prefixLift 8303269
  have htrace : WordTrace (prefixWord ++ tailWord_8303269) baseStart_8303269 baseEnd_8303269 := by
    simpa [prefixWord, tailWord_8303269, baseEnd_8303269] using wordTrace_append hprefix tailTrace_8303269
  have hstable : (prefixWord ++ tailWord_8303269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303269).length < 2 ^ (prefixWord ++ tailWord_8303269).sum := by decide
  have hdescent : baseEnd_8303269 < baseStart_8303269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303316 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_8303316 : Nat := 118140960795 + 8303316 * 2 ^ 59
def prefixEnd_8303316 : Nat := 4983230072969 + 3 ^ 40 * 8303316 * 2
def baseEnd_8303316 : Nat := 4263592134167940471663751

theorem tailTrace_8303316 : CollatzResearch.WordTrace tailWord_8303316 prefixEnd_8303316 4263592134167940471663751 := by
  unfold tailWord_8303316
  simp only [CollatzResearch.WordTrace]
  refine ⟨151423407193255850158860901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201897876257674466878481201 151423407193255850158860901)
  ·
    refine ⟨28391888848735471904786419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151423407193255850158860901 28391888848735471904786419)
    ·
      refine ⟨42587833273103207857179629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28391888848735471904786419 42587833273103207857179629)
      ·
        refine ⟨15970437477413702946442361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42587833273103207857179629 15970437477413702946442361)
        ·
          refine ⟨11977828108060277209831771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15970437477413702946442361 11977828108060277209831771)
          ·
            refine ⟨17966742162090415814747657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11977828108060277209831771 17966742162090415814747657)
            ·
              refine ⟨13475056621567811861060743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17966742162090415814747657 13475056621567811861060743)
              ·
                refine ⟨20212584932351717791591115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475056621567811861060743 20212584932351717791591115)
                ·
                  refine ⟨30318877398527576687386673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20212584932351717791591115 30318877398527576687386673)
                  ·
                    refine ⟨22739158048895682515540005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30318877398527576687386673 22739158048895682515540005)
                    ·
                      refine ⟨4263592134167940471663751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22739158048895682515540005 4263592134167940471663751)
                      ·
                        rfl

theorem cell23_8303316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_8303316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303316 prefixEnd_8303316 := by exact prefixLift 8303316
  have htrace : WordTrace (prefixWord ++ tailWord_8303316) baseStart_8303316 baseEnd_8303316 := by
    simpa [prefixWord, tailWord_8303316, baseEnd_8303316] using wordTrace_append hprefix tailTrace_8303316
  have hstable : (prefixWord ++ tailWord_8303316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303316).length < 2 ^ (prefixWord ++ tailWord_8303316).sum := by decide
  have hdescent : baseEnd_8303316 < baseStart_8303316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303319 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_8303319 : Nat := 118140960795 + 8303319 * 2 ^ 59
def prefixEnd_8303319 : Nat := 4983230072969 + 3 ^ 40 * 8303319 * 2
def baseEnd_8303319 : Nat := 4263593674609903959926237

theorem tailTrace_8303319 : CollatzResearch.WordTrace tailWord_8303319 prefixEnd_8303319 4263593674609903959926237 := by
  unfold tailWord_8303319
  simp only [CollatzResearch.WordTrace]
  refine ⟨302846923805500831830081011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201897949203667221220054007 302846923805500831830081011)
  ·
    refine ⟨454270385708251247745121517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302846923805500831830081011 454270385708251247745121517)
    ·
      refine ⟨170351394640594217904420569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454270385708251247745121517 170351394640594217904420569)
      ·
        refine ⟨127763545980445663428315427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170351394640594217904420569 127763545980445663428315427)
        ·
          refine ⟨191645318970668495142473141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127763545980445663428315427 191645318970668495142473141)
          ·
            refine ⟨17966748653500171419606857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191645318970668495142473141 17966748653500171419606857)
            ·
              refine ⟨13475061490125128564705143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17966748653500171419606857 13475061490125128564705143)
              ·
                refine ⟨20212592235187692847057715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475061490125128564705143 20212592235187692847057715)
                ·
                  refine ⟨30318888352781539270586573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20212592235187692847057715 30318888352781539270586573)
                  ·
                    refine ⟨11369583132293077226469965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30318888352781539270586573 11369583132293077226469965)
                    ·
                      refine ⟨4263593674609903959926237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11369583132293077226469965 4263593674609903959926237)
                      ·
                        rfl

theorem cell23_8303319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_8303319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303319 prefixEnd_8303319 := by exact prefixLift 8303319
  have htrace : WordTrace (prefixWord ++ tailWord_8303319) baseStart_8303319 baseEnd_8303319 := by
    simpa [prefixWord, tailWord_8303319, baseEnd_8303319] using wordTrace_append hprefix tailTrace_8303319
  have hstable : (prefixWord ++ tailWord_8303319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303319).length < 2 ^ (prefixWord ++ tailWord_8303319).sum := by decide
  have hdescent : baseEnd_8303319 < baseStart_8303319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303416 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 5]
def baseStart_8303416 : Nat := 118140960795 + 8303416 * 2 ^ 59
def prefixEnd_8303416 : Nat := 4983230072969 + 3 ^ 40 * 8303416 * 2
def baseEnd_8303416 : Nat := 473738164692598897823699

theorem tailTrace_8303416 : CollatzResearch.WordTrace tailWord_8303416 prefixEnd_8303416 473738164692598897823699 := by
  unfold tailWord_8303416
  simp only [CollatzResearch.WordTrace]
  refine ⟨151425230843074708698181051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201900307790766278264241401 151425230843074708698181051)
  ·
    refine ⟨227137846264612063047271577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151425230843074708698181051 227137846264612063047271577)
    ·
      refine ⟨170353384698459047285453683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227137846264612063047271577 170353384698459047285453683)
      ·
        refine ⟨255530077047688570928180525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170353384698459047285453683 255530077047688570928180525)
        ·
          refine ⟨95823778892883214098067697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255530077047688570928180525 95823778892883214098067697)
          ·
            refine ⟨71867834169662410573550773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95823778892883214098067697 71867834169662410573550773)
            ·
              refine ⟨6737609453405850991270385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71867834169662410573550773 6737609453405850991270385)
              ·
                refine ⟨5053207090054388243452789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737609453405850991270385 5053207090054388243452789)
                ·
                  refine ⟨473738164692598897823699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053207090054388243452789 473738164692598897823699)
                  ·
                    rfl

theorem cell23_8303416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 5].length) (baseStart_8303416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303416 prefixEnd_8303416 := by exact prefixLift 8303416
  have htrace : WordTrace (prefixWord ++ tailWord_8303416) baseStart_8303416 baseEnd_8303416 := by
    simpa [prefixWord, tailWord_8303416, baseEnd_8303416] using wordTrace_append hprefix tailTrace_8303416
  have hstable : (prefixWord ++ tailWord_8303416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303416).length < 2 ^ (prefixWord ++ tailWord_8303416).sum := by decide
  have hdescent : baseEnd_8303416 < baseStart_8303416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303449 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_8303449 : Nat := 118140960795 + 8303449 * 2 ^ 59
def prefixEnd_8303449 : Nat := 4983230072969 + 3 ^ 40 * 8303449 * 2
def baseEnd_8303449 : Nat := 4263660427094988451300639

theorem tailTrace_8303449 : CollatzResearch.WordTrace tailWord_8303449 prefixEnd_8303449 4263660427094988451300639 := by
  unfold tailWord_8303449
  simp only [CollatzResearch.WordTrace]
  refine ⟨302851665295029864032313401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201901110196686576021542267 302851665295029864032313401)
  ·
    refine ⟨227138748971272398024235051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302851665295029864032313401 227138748971272398024235051)
    ·
      refine ⟨340708123456908597036352577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227138748971272398024235051 340708123456908597036352577)
      ·
        refine ⟨255531092592681447777264433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340708123456908597036352577 255531092592681447777264433)
        ·
          refine ⟨191648319444511085832948325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255531092592681447777264433 191648319444511085832948325)
          ·
            refine ⟨35934059895845828593677811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191648319444511085832948325 35934059895845828593677811)
            ·
              refine ⟨53901089843768742890516717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35934059895845828593677811 53901089843768742890516717)
              ·
                refine ⟨20212908691413278583943769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53901089843768742890516717 20212908691413278583943769)
                ·
                  refine ⟨15159681518559958937957827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20212908691413278583943769 15159681518559958937957827)
                  ·
                    refine ⟨22739522277839938406936741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15159681518559958937957827 22739522277839938406936741)
                    ·
                      refine ⟨4263660427094988451300639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22739522277839938406936741 4263660427094988451300639)
                      ·
                        rfl

theorem cell23_8303449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_8303449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303449 prefixEnd_8303449 := by exact prefixLift 8303449
  have htrace : WordTrace (prefixWord ++ tailWord_8303449) baseStart_8303449 baseEnd_8303449 := by
    simpa [prefixWord, tailWord_8303449, baseEnd_8303449] using wordTrace_append hprefix tailTrace_8303449
  have hstable : (prefixWord ++ tailWord_8303449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303449).length < 2 ^ (prefixWord ++ tailWord_8303449).sum := by decide
  have hdescent : baseEnd_8303449 < baseStart_8303449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303469 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_8303469 : Nat := 118140960795 + 8303469 * 2 ^ 59
def prefixEnd_8303469 : Nat := 4983230072969 + 3 ^ 40 * 8303469 * 2
def baseEnd_8303469 : Nat := 4263670696708078373050547

theorem tailTrace_8303469 : CollatzResearch.WordTrace tailWord_8303469 prefixEnd_8303469 4263670696708078373050547 := by
  unfold tailWord_8303469
  simp only [CollatzResearch.WordTrace]
  refine ⟨302852394754957407448041461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201901596503304938298694307 302852394754957407448041461)
  ·
    refine ⟨28392412008277256948253887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302852394754957407448041461 28392412008277256948253887)
    ·
      refine ⟨42588618012415885422380831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392412008277256948253887 42588618012415885422380831)
      ·
        refine ⟨63882927018623828133571247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42588618012415885422380831 63882927018623828133571247)
        ·
          refine ⟨95824390527935742200356871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63882927018623828133571247 95824390527935742200356871)
          ·
            refine ⟨143736585791903613300535307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95824390527935742200356871 143736585791903613300535307)
            ·
              refine ⟨215604878687855419950802961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143736585791903613300535307 215604878687855419950802961)
              ·
                refine ⟨161703659015891564963102221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215604878687855419950802961 161703659015891564963102221)
                ·
                  refine ⟨60638872130959336861163333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161703659015891564963102221 60638872130959336861163333)
                  ·
                    refine ⟨11369788524554875661468125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60638872130959336861163333 11369788524554875661468125)
                    ·
                      refine ⟨4263670696708078373050547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11369788524554875661468125 4263670696708078373050547)
                      ·
                        rfl

theorem cell23_8303469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_8303469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303469 prefixEnd_8303469 := by exact prefixLift 8303469
  have htrace : WordTrace (prefixWord ++ tailWord_8303469) baseStart_8303469 baseEnd_8303469 := by
    simpa [prefixWord, tailWord_8303469, baseEnd_8303469] using wordTrace_append hprefix tailTrace_8303469
  have hstable : (prefixWord ++ tailWord_8303469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303469).length < 2 ^ (prefixWord ++ tailWord_8303469).sum := by decide
  have hdescent : baseEnd_8303469 < baseStart_8303469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303472 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 8]
def baseStart_8303472 : Nat := 118140960795 + 8303472 * 2 ^ 59
def prefixEnd_8303472 : Nat := 4983230072969 + 3 ^ 40 * 8303472 * 2
def baseEnd_8303472 : Nat := 473741359683337984590337

theorem tailTrace_8303472 : CollatzResearch.WordTrace tailWord_8303472 prefixEnd_8303472 473741359683337984590337 := by
  unfold tailWord_8303472
  simp only [CollatzResearch.WordTrace]
  refine ⟨151426252086973269480200335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201901669449297692640267113 151426252086973269480200335)
  ·
    refine ⟨227139378130459904220300503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151426252086973269480200335 227139378130459904220300503)
    ·
      refine ⟨340709067195689856330450755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227139378130459904220300503 340709067195689856330450755)
      ·
        refine ⟨511063600793534784495676133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340709067195689856330450755 511063600793534784495676133)
        ·
          refine ⟨95824425148787772092939275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511063600793534784495676133 95824425148787772092939275)
          ·
            refine ⟨143736637723181658139408913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95824425148787772092939275 143736637723181658139408913)
            ·
              refine ⟨107802478292386243604556685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143736637723181658139408913 107802478292386243604556685)
              ·
                refine ⟨40425929359644841351708757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107802478292386243604556685 40425929359644841351708757)
                ·
                  refine ⟨473741359683337984590337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40425929359644841351708757 473741359683337984590337)
                  ·
                    rfl

theorem cell23_8303472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_8303472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303472 prefixEnd_8303472 := by exact prefixLift 8303472
  have htrace : WordTrace (prefixWord ++ tailWord_8303472) baseStart_8303472 baseEnd_8303472 := by
    simpa [prefixWord, tailWord_8303472, baseEnd_8303472] using wordTrace_append hprefix tailTrace_8303472
  have hstable : (prefixWord ++ tailWord_8303472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303472).length < 2 ^ (prefixWord ++ tailWord_8303472).sum := by decide
  have hdescent : baseEnd_8303472 < baseStart_8303472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303539 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4]
def baseStart_8303539 : Nat := 118140960795 + 8303539 * 2 ^ 59
def prefixEnd_8303539 : Nat := 4983230072969 + 3 ^ 40 * 8303539 * 2
def baseEnd_8303539 : Nat := 4263706640353893099175225

theorem tailTrace_8303539 : CollatzResearch.WordTrace tailWord_8303539 prefixEnd_8303539 4263706640353893099175225 := by
  unfold tailWord_8303539
  simp only [CollatzResearch.WordTrace]
  refine ⟨302854947864703809403089671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201903298576469206268726447 302854947864703809403089671)
  ·
    refine ⟨454282421797055714104634507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302854947864703809403089671 454282421797055714104634507)
    ·
      refine ⟨681423632695583571156951761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454282421797055714104634507 681423632695583571156951761)
      ·
        refine ⟨511067724521687678367713821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681423632695583571156951761 511067724521687678367713821)
        ·
          refine ⟨191650396695632879387892683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511067724521687678367713821 191650396695632879387892683)
          ·
            refine ⟨287475595043449319081839025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191650396695632879387892683 287475595043449319081839025)
            ·
              refine ⟨215606696282586989311379269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287475595043449319081839025 215606696282586989311379269)
              ·
                refine ⟨40426255552985060495883613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215606696282586989311379269 40426255552985060495883613)
                ·
                  refine ⟨15159845832369397685956355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40426255552985060495883613 15159845832369397685956355)
                  ·
                    refine ⟨22739768748554096528934533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15159845832369397685956355 22739768748554096528934533)
                    ·
                      refine ⟨4263706640353893099175225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22739768748554096528934533 4263706640353893099175225)
                      ·
                        rfl

theorem cell23_8303539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_8303539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303539 prefixEnd_8303539 := by exact prefixLift 8303539
  have htrace : WordTrace (prefixWord ++ tailWord_8303539) baseStart_8303539 baseEnd_8303539 := by
    simpa [prefixWord, tailWord_8303539, baseEnd_8303539] using wordTrace_append hprefix tailTrace_8303539
  have hstable : (prefixWord ++ tailWord_8303539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303539).length < 2 ^ (prefixWord ++ tailWord_8303539).sum := by decide
  have hdescent : baseEnd_8303539 < baseStart_8303539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303540 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 6]
def baseStart_8303540 : Nat := 118140960795 + 8303540 * 2 ^ 59
def prefixEnd_8303540 : Nat := 4983230072969 + 3 ^ 40 * 8303540 * 2
def baseEnd_8303540 : Nat := 473745239314949732806969

theorem tailTrace_8303540 : CollatzResearch.WordTrace tailWord_8303540 prefixEnd_8303540 473745239314949732806969 := by
  unfold tailWord_8303540
  simp only [CollatzResearch.WordTrace]
  refine ⟨151427492168850093286938037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201903322891800124382584049 151427492168850093286938037)
  ·
    refine ⟨14196327390829696245650441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151427492168850093286938037 14196327390829696245650441)
    ·
      refine ⟨10647245543122272184237831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14196327390829696245650441 10647245543122272184237831)
      ·
        refine ⟨15970868314683408276356747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647245543122272184237831 15970868314683408276356747)
        ·
          refine ⟨23956302472025112414535121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15970868314683408276356747 23956302472025112414535121)
          ·
            refine ⟨17967226854018834310901341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23956302472025112414535121 17967226854018834310901341)
            ·
              refine ⟨6737710070257062866588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17967226854018834310901341 6737710070257062866588003)
              ·
                refine ⟨10106565105385594299882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6737710070257062866588003 10106565105385594299882005)
                ·
                  refine ⟨473745239314949732806969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10106565105385594299882005 473745239314949732806969)
                  ·
                    rfl

theorem cell23_8303540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_8303540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303540 prefixEnd_8303540 := by exact prefixLift 8303540
  have htrace : WordTrace (prefixWord ++ tailWord_8303540) baseStart_8303540 baseEnd_8303540 := by
    simpa [prefixWord, tailWord_8303540, baseEnd_8303540] using wordTrace_append hprefix tailTrace_8303540
  have hstable : (prefixWord ++ tailWord_8303540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303540).length < 2 ^ (prefixWord ++ tailWord_8303540).sum := by decide
  have hdescent : baseEnd_8303540 < baseStart_8303540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303566 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_8303566 : Nat := 118140960795 + 8303566 * 2 ^ 59
def prefixEnd_8303566 : Nat := 4983230072969 + 3 ^ 40 * 8303566 * 2
def baseEnd_8303566 : Nat := 1421240168110521497845867

theorem tailTrace_8303566 : CollatzResearch.WordTrace tailWord_8303566 prefixEnd_8303566 1421240168110521497845867 := by
  unfold tailWord_8303566
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856991579450749126790319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201903955090403995342881701 37856991579450749126790319)
  ·
    refine ⟨56785487369176123690185479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37856991579450749126790319 56785487369176123690185479)
    ·
      refine ⟨85178231053764185535278219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56785487369176123690185479 85178231053764185535278219)
      ·
        refine ⟨127767346580646278302917329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85178231053764185535278219 127767346580646278302917329)
        ·
          refine ⟨95825509935484708727187997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127767346580646278302917329 95825509935484708727187997)
          ·
            refine ⟨35934566225806765772695499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95825509935484708727187997 35934566225806765772695499)
            ·
              refine ⟨53901849338710148659043249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35934566225806765772695499 53901849338710148659043249)
              ·
                refine ⟨40426387004032611494282437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53901849338710148659043249 40426387004032611494282437)
                ·
                  refine ⟨7579947563256114655177957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40426387004032611494282437 7579947563256114655177957)
                  ·
                    refine ⟨1421240168110521497845867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7579947563256114655177957 1421240168110521497845867)
                    ·
                      rfl

theorem cell23_8303566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_8303566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303566 prefixEnd_8303566 := by exact prefixLift 8303566
  have htrace : WordTrace (prefixWord ++ tailWord_8303566) baseStart_8303566 baseEnd_8303566 := by
    simpa [prefixWord, tailWord_8303566, baseEnd_8303566] using wordTrace_append hprefix tailTrace_8303566
  have hstable : (prefixWord ++ tailWord_8303566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303566).length < 2 ^ (prefixWord ++ tailWord_8303566).sum := by decide
  have hdescent : baseEnd_8303566 < baseStart_8303566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303569 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_8303569 : Nat := 118140960795 + 8303569 * 2 ^ 59
def prefixEnd_8303569 : Nat := 4983230072969 + 3 ^ 40 * 8303569 * 2
def baseEnd_8303569 : Nat := 4263722044773527981800087

theorem tailTrace_8303569 : CollatzResearch.WordTrace tailWord_8303569 prefixEnd_8303569 4263722044773527981800087 := by
  unfold tailWord_8303569
  simp only [CollatzResearch.WordTrace]
  refine ⟨302856042054595124526681761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201904028036396749684454507 302856042054595124526681761)
  ·
    refine ⟨227142031540946343395011321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302856042054595124526681761 227142031540946343395011321)
    ·
      refine ⟨170356523655709757546258491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227142031540946343395011321 170356523655709757546258491)
      ·
        refine ⟨255534785483564636319387737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170356523655709757546258491 255534785483564636319387737)
        ·
          refine ⟨191651089112673477239540803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255534785483564636319387737 191651089112673477239540803)
          ·
            refine ⟨287476633669010215859311205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191651089112673477239540803 287476633669010215859311205)
            ·
              refine ⟨53901868812939415473620851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287476633669010215859311205 53901868812939415473620851)
              ·
                refine ⟨80852803219409123210431277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53901868812939415473620851 80852803219409123210431277)
                ·
                  refine ⟨30319801207278421203911729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80852803219409123210431277 30319801207278421203911729)
                  ·
                    refine ⟨22739850905458815902933797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30319801207278421203911729 22739850905458815902933797)
                    ·
                      refine ⟨4263722044773527981800087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22739850905458815902933797 4263722044773527981800087)
                      ·
                        rfl

theorem cell23_8303569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_8303569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303569 prefixEnd_8303569 := by exact prefixLift 8303569
  have htrace : WordTrace (prefixWord ++ tailWord_8303569) baseStart_8303569 baseEnd_8303569 := by
    simpa [prefixWord, tailWord_8303569, baseEnd_8303569] using wordTrace_append hprefix tailTrace_8303569
  have hstable : (prefixWord ++ tailWord_8303569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303569).length < 2 ^ (prefixWord ++ tailWord_8303569).sum := by decide
  have hdescent : baseEnd_8303569 < baseStart_8303569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303576 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_8303576 : Nat := 118140960795 + 8303576 * 2 ^ 59
def prefixEnd_8303576 : Nat := 4983230072969 + 3 ^ 40 * 8303576 * 2
def baseEnd_8303576 : Nat := 4263725639138109454412555

theorem tailTrace_8303576 : CollatzResearch.WordTrace tailWord_8303576 prefixEnd_8303576 4263725639138109454412555 := by
  unfold tailWord_8303576
  simp only [CollatzResearch.WordTrace]
  refine ⟨151428148682784882361093291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201904198243713176481457721 151428148682784882361093291)
  ·
    refine ⟨227142223024177323541639937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151428148682784882361093291 227142223024177323541639937)
    ·
      refine ⟨170356667268132992656229953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227142223024177323541639937 170356667268132992656229953)
      ·
        refine ⟨127767500451099744492172465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170356667268132992656229953 127767500451099744492172465)
        ·
          refine ⟨95825625338324808369129349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127767500451099744492172465 95825625338324808369129349)
          ·
            refine ⟨17967304750935901569211753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95825625338324808369129349 17967304750935901569211753)
            ·
              refine ⟨13475478563201926176908815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17967304750935901569211753 13475478563201926176908815)
              ·
                refine ⟨20213217844802889265363223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475478563201926176908815 20213217844802889265363223)
                ·
                  refine ⟨30319826767204333898044835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20213217844802889265363223 30319826767204333898044835)
                  ·
                    refine ⟨45479740150806500847067253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30319826767204333898044835 45479740150806500847067253)
                    ·
                      refine ⟨4263725639138109454412555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45479740150806500847067253 4263725639138109454412555)
                      ·
                        rfl

theorem cell23_8303576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_8303576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303576 prefixEnd_8303576 := by exact prefixLift 8303576
  have htrace : WordTrace (prefixWord ++ tailWord_8303576) baseStart_8303576 baseEnd_8303576 := by
    simpa [prefixWord, tailWord_8303576, baseEnd_8303576] using wordTrace_append hprefix tailTrace_8303576
  have hstable : (prefixWord ++ tailWord_8303576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303576).length < 2 ^ (prefixWord ++ tailWord_8303576).sum := by decide
  have hdescent : baseEnd_8303576 < baseStart_8303576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303633 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_8303633 : Nat := 118140960795 + 8303633 * 2 ^ 59
def prefixEnd_8303633 : Nat := 4983230072969 + 3 ^ 40 * 8303633 * 2
def baseEnd_8303633 : Nat := 4263754907535415731399793

theorem tailTrace_8303633 : CollatzResearch.WordTrace tailWord_8303633 prefixEnd_8303633 4263754907535415731399793 := by
  unfold tailWord_8303633
  simp only [CollatzResearch.WordTrace]
  refine ⟨302858376326363263457011553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201905584217575508971341035 302858376326363263457011553)
  ·
    refine ⟨227143782244772447592758665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302858376326363263457011553 227143782244772447592758665)
    ·
      refine ⟨170357836683579335694568999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227143782244772447592758665 170357836683579335694568999)
      ·
        refine ⟨255536755025369003541853499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170357836683579335694568999 255536755025369003541853499)
        ·
          refine ⟨383305132538053505312780249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255536755025369003541853499 383305132538053505312780249)
          ·
            refine ⟨287478849403540128984585187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383305132538053505312780249 287478849403540128984585187)
            ·
              refine ⟨431218274105310193476877781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287478849403540128984585187 431218274105310193476877781)
              ·
                refine ⟨10106678299343207659614323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431218274105310193476877781 10106678299343207659614323)
                ·
                  refine ⟨15160017449014811489421485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10106678299343207659614323 15160017449014811489421485)
                  ·
                    refine ⟨5685006543380554308533057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15160017449014811489421485 5685006543380554308533057)
                    ·
                      refine ⟨4263754907535415731399793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685006543380554308533057 4263754907535415731399793)
                      ·
                        rfl

theorem cell23_8303633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_8303633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303633 prefixEnd_8303633 := by exact prefixLift 8303633
  have htrace : WordTrace (prefixWord ++ tailWord_8303633) baseStart_8303633 baseEnd_8303633 := by
    simpa [prefixWord, tailWord_8303633, baseEnd_8303633] using wordTrace_append hprefix tailTrace_8303633
  have hstable : (prefixWord ++ tailWord_8303633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303633).length < 2 ^ (prefixWord ++ tailWord_8303633).sum := by decide
  have hdescent : baseEnd_8303633 < baseStart_8303633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303634 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_8303634 : Nat := 118140960795 + 8303634 * 2 ^ 59
def prefixEnd_8303634 : Nat := 4983230072969 + 3 ^ 40 * 8303634 * 2
def baseEnd_8303634 : Nat := 1421251807005356742495763

theorem tailTrace_8303634 : CollatzResearch.WordTrace tailWord_8303634 prefixEnd_8303634 1421251807005356742495763 := by
  unfold tailWord_8303634
  simp only [CollatzResearch.WordTrace]
  refine ⟨75714603199839910156949489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201905608532906427085198637 75714603199839910156949489)
  ·
    refine ⟨56785952399879932617712117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75714603199839910156949489 56785952399879932617712117)
    ·
      refine ⟨5323683037488743682910511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56785952399879932617712117 5323683037488743682910511)
      ·
        refine ⟨7985524556233115524365767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323683037488743682910511 7985524556233115524365767)
        ·
          refine ⟨11978286834349673286548651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7985524556233115524365767 11978286834349673286548651)
          ·
            refine ⟨17967430251524509929822977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978286834349673286548651 17967430251524509929822977)
            ·
              refine ⟨13475572688643382447367233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17967430251524509929822977 13475572688643382447367233)
              ·
                refine ⟨10106679516482536835525425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13475572688643382447367233 10106679516482536835525425)
                ·
                  refine ⟨7580009637361902626644069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10106679516482536835525425 7580009637361902626644069)
                  ·
                    refine ⟨1421251807005356742495763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580009637361902626644069 1421251807005356742495763)
                    ·
                      rfl

theorem cell23_8303634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_8303634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303634 prefixEnd_8303634 := by exact prefixLift 8303634
  have htrace : WordTrace (prefixWord ++ tailWord_8303634) baseStart_8303634 baseEnd_8303634 := by
    simpa [prefixWord, tailWord_8303634, baseEnd_8303634] using wordTrace_append hprefix tailTrace_8303634
  have hstable : (prefixWord ++ tailWord_8303634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303634).length < 2 ^ (prefixWord ++ tailWord_8303634).sum := by decide
  have hdescent : baseEnd_8303634 < baseStart_8303634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303640 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_8303640 : Nat := 118140960795 + 8303640 * 2 ^ 59
def prefixEnd_8303640 : Nat := 4983230072969 + 3 ^ 40 * 8303640 * 2
def baseEnd_8303640 : Nat := 4263758501899997204012261

theorem tailTrace_8303640 : CollatzResearch.WordTrace tailWord_8303640 prefixEnd_8303640 4263758501899997204012261 := by
  unfold tailWord_8303640
  simp only [CollatzResearch.WordTrace]
  refine ⟨151429315818668951826258187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201905754424891935768344249 151429315818668951826258187)
  ·
    refine ⟨227143973728003427739387281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151429315818668951826258187 227143973728003427739387281)
    ·
      refine ⟨170357980296002570804540461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227143973728003427739387281 170357980296002570804540461)
      ·
        refine ⟨63884242611000964051702673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170357980296002570804540461 63884242611000964051702673)
        ·
          refine ⟨47913181958250723038777005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63884242611000964051702673 47913181958250723038777005)
          ·
            refine ⟨17967443234344021139541377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47913181958250723038777005 17967443234344021139541377)
            ·
              refine ⟨13475582425758015854656033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17967443234344021139541377 13475582425758015854656033)
              ·
                refine ⟨10106686819318511890992025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13475582425758015854656033 10106686819318511890992025)
                ·
                  refine ⟨7580015114488883918244019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10106686819318511890992025 7580015114488883918244019)
                  ·
                    refine ⟨11370022671733325877366029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580015114488883918244019 11370022671733325877366029)
                    ·
                      refine ⟨4263758501899997204012261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11370022671733325877366029 4263758501899997204012261)
                      ·
                        rfl

theorem cell23_8303640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_8303640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303640 prefixEnd_8303640 := by exact prefixLift 8303640
  have htrace : WordTrace (prefixWord ++ tailWord_8303640) baseStart_8303640 baseEnd_8303640 := by
    simpa [prefixWord, tailWord_8303640, baseEnd_8303640] using wordTrace_append hprefix tailTrace_8303640
  have hstable : (prefixWord ++ tailWord_8303640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303640).length < 2 ^ (prefixWord ++ tailWord_8303640).sum := by decide
  have hdescent : baseEnd_8303640 < baseStart_8303640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303666 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_8303666 : Nat := 118140960795 + 8303666 * 2 ^ 59
def prefixEnd_8303666 : Nat := 4983230072969 + 3 ^ 40 * 8303666 * 2
def baseEnd_8303666 : Nat := 4263771852397014102287141

theorem tailTrace_8303666 : CollatzResearch.WordTrace tailWord_8303666 prefixEnd_8303666 4263771852397014102287141 := by
  unfold tailWord_8303666
  simp only [CollatzResearch.WordTrace]
  refine ⟨75714894983810927523240713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201906386623495806728641901 75714894983810927523240713)
  ·
    refine ⟨56786171237858195642430535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75714894983810927523240713 56786171237858195642430535)
    ·
      refine ⟨85179256856787293463645803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56786171237858195642430535 85179256856787293463645803)
      ·
        refine ⟨127768885285180940195468705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85179256856787293463645803 127768885285180940195468705)
        ·
          refine ⟨95826663963885705146601529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127768885285180940195468705 95826663963885705146601529)
          ·
            refine ⟨71869997972914278859951147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95826663963885705146601529 71869997972914278859951147)
            ·
              refine ⟨107804996959371418289926721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71869997972914278859951147 107804996959371418289926721)
              ·
                refine ⟨80853747719528563717445041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107804996959371418289926721 80853747719528563717445041)
                ·
                  refine ⟨60640310789646422788083781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80853747719528563717445041 60640310789646422788083781)
                  ·
                    refine ⟨11370058273058704272765709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60640310789646422788083781 11370058273058704272765709)
                    ·
                      refine ⟨4263771852397014102287141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11370058273058704272765709 4263771852397014102287141)
                      ·
                        rfl

theorem cell23_8303666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_8303666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303666 prefixEnd_8303666 := by exact prefixLift 8303666
  have htrace : WordTrace (prefixWord ++ tailWord_8303666) baseStart_8303666 baseEnd_8303666 := by
    simpa [prefixWord, tailWord_8303666, baseEnd_8303666] using wordTrace_append hprefix tailTrace_8303666
  have hstable : (prefixWord ++ tailWord_8303666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303666).length < 2 ^ (prefixWord ++ tailWord_8303666).sum := by decide
  have hdescent : baseEnd_8303666 < baseStart_8303666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303679 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_8303679 : Nat := 118140960795 + 8303679 * 2 ^ 59
def prefixEnd_8303679 : Nat := 4983230072969 + 3 ^ 40 * 8303679 * 2
def baseEnd_8303679 : Nat := 4263778527645522551424581

theorem tailTrace_8303679 : CollatzResearch.WordTrace tailWord_8303679 prefixEnd_8303679 4263778527645522551424581 := by
  unfold tailWord_8303679
  simp only [CollatzResearch.WordTrace]
  refine ⟨302860054084196613313186091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201906702722797742208790727 302860054084196613313186091)
  ·
    refine ⟨454290081126294919969779137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302860054084196613313186091 454290081126294919969779137)
    ·
      refine ⟨340717560844721189977334353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454290081126294919969779137 340717560844721189977334353)
      ·
        refine ⟨255538170633540892483000765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340717560844721189977334353 255538170633540892483000765)
        ·
          refine ⟨95826813987577834681125287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255538170633540892483000765 95826813987577834681125287)
          ·
            refine ⟨143740220981366752021687931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95826813987577834681125287 143740220981366752021687931)
            ·
              refine ⟨215610331472050128032531897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143740220981366752021687931 215610331472050128032531897)
              ·
                refine ⟨161707748604037596024398923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215610331472050128032531897 161707748604037596024398923)
                ·
                  refine ⟨242561622906056394036598385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161707748604037596024398923 242561622906056394036598385)
                  ·
                    refine ⟨181921217179542295527448789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242561622906056394036598385 181921217179542295527448789)
                    ·
                      refine ⟨4263778527645522551424581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181921217179542295527448789 4263778527645522551424581)
                      ·
                        rfl

theorem cell23_8303679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_8303679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303679 prefixEnd_8303679 := by exact prefixLift 8303679
  have htrace : WordTrace (prefixWord ++ tailWord_8303679) baseStart_8303679 baseEnd_8303679 := by
    simpa [prefixWord, tailWord_8303679, baseEnd_8303679] using wordTrace_append hprefix tailTrace_8303679
  have hstable : (prefixWord ++ tailWord_8303679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303679).length < 2 ^ (prefixWord ++ tailWord_8303679).sum := by decide
  have hdescent : baseEnd_8303679 < baseStart_8303679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303693 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_8303693 : Nat := 118140960795 + 8303693 * 2 ^ 59
def prefixEnd_8303693 : Nat := 4983230072969 + 3 ^ 40 * 8303693 * 2
def baseEnd_8303693 : Nat := 4263785716374685496649517

theorem tailTrace_8303693 : CollatzResearch.WordTrace tailWord_8303693 prefixEnd_8303693 4263785716374685496649517 := by
  unfold tailWord_8303693
  simp only [CollatzResearch.WordTrace]
  refine ⟨302860564706145893704195733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201907043137430595802797155 302860564706145893704195733)
  ·
    refine ⟨14196588970600588767384175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302860564706145893704195733 14196588970600588767384175)
    ·
      refine ⟨21294883455900883151076263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14196588970600588767384175 21294883455900883151076263)
      ·
        refine ⟨31942325183851324726614395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21294883455900883151076263 31942325183851324726614395)
        ·
          refine ⟨47913487775776987089921593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31942325183851324726614395 47913487775776987089921593)
          ·
            refine ⟨35935115831832740317441195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47913487775776987089921593 35935115831832740317441195)
            ·
              refine ⟨53902673747749110476161793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35935115831832740317441195 53902673747749110476161793)
              ·
                refine ⟨40427005310811832857121345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53902673747749110476161793 40427005310811832857121345)
                ·
                  refine ⟨30320253983108874642841009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40427005310811832857121345 30320253983108874642841009)
                  ·
                    refine ⟨22740190487331655982130757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30320253983108874642841009 22740190487331655982130757)
                    ·
                      refine ⟨4263785716374685496649517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22740190487331655982130757 4263785716374685496649517)
                      ·
                        rfl

theorem cell23_8303693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_8303693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303693 prefixEnd_8303693 := by exact prefixLift 8303693
  have htrace : WordTrace (prefixWord ++ tailWord_8303693) baseStart_8303693 baseEnd_8303693 := by
    simpa [prefixWord, tailWord_8303693, baseEnd_8303693] using wordTrace_append hprefix tailTrace_8303693
  have hstable : (prefixWord ++ tailWord_8303693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303693).length < 2 ^ (prefixWord ++ tailWord_8303693).sum := by decide
  have hdescent : baseEnd_8303693 < baseStart_8303693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303699 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 7]
def baseStart_8303699 : Nat := 118140960795 + 8303699 * 2 ^ 59
def prefixEnd_8303699 : Nat := 4983230072969 + 3 ^ 40 * 8303699 * 2
def baseEnd_8303699 : Nat := 1421262932419537491058163

theorem tailTrace_8303699 : CollatzResearch.WordTrace tailWord_8303699 prefixEnd_8303699 1421262932419537491058163 := by
  unfold tailWord_8303699
  simp only [CollatzResearch.WordTrace]
  refine ⟨302860783544124156728914151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201907189029416104485942767 302860783544124156728914151)
  ·
    refine ⟨454291175316186235093371227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302860783544124156728914151 454291175316186235093371227)
    ·
      refine ⟨681436762974279352640056841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454291175316186235093371227 681436762974279352640056841)
      ·
        refine ⟨511077572230709514480042631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681436762974279352640056841 511077572230709514480042631)
        ·
          refine ⟨766616358346064271720063947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511077572230709514480042631 766616358346064271720063947)
          ·
            refine ⟨1149924537519096407580095921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766616358346064271720063947 1149924537519096407580095921)
            ·
              refine ⟨862443403139322305685071941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149924537519096407580095921 862443403139322305685071941)
              ·
                refine ⟨161708138088622932315950989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 862443403139322305685071941 161708138088622932315950989)
                ·
                  refine ⟨60640551783233599618481621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161708138088622932315950989 60640551783233599618481621)
                  ·
                    refine ⟨1421262932419537491058163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60640551783233599618481621 1421262932419537491058163)
                    ·
                      rfl

theorem cell23_8303699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_8303699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303699 prefixEnd_8303699 := by exact prefixLift 8303699
  have htrace : WordTrace (prefixWord ++ tailWord_8303699) baseStart_8303699 baseEnd_8303699 := by
    simpa [prefixWord, tailWord_8303699, baseEnd_8303699] using wordTrace_append hprefix tailTrace_8303699
  have hstable : (prefixWord ++ tailWord_8303699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303699).length < 2 ^ (prefixWord ++ tailWord_8303699).sum := by decide
  have hdescent : baseEnd_8303699 < baseStart_8303699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303736 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_8303736 : Nat := 118140960795 + 8303736 * 2 ^ 59
def prefixEnd_8303736 : Nat := 4983230072969 + 3 ^ 40 * 8303736 * 2
def baseEnd_8303736 : Nat := 4263807796042828828411819

theorem tailTrace_8303736 : CollatzResearch.WordTrace tailWord_8303736 prefixEnd_8303736 4263807796042828828411819 := by
  unfold tailWord_8303736
  simp only [CollatzResearch.WordTrace]
  refine ⟨151431066522495056024005531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201908088696660074698674041 151431066522495056024005531)
  ·
    refine ⟨227146599783742584036008297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151431066522495056024005531 227146599783742584036008297)
    ·
      refine ⟨170359949837806938027006223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227146599783742584036008297 170359949837806938027006223)
      ·
        refine ⟨255539924756710407040509335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170359949837806938027006223 255539924756710407040509335)
        ·
          refine ⟨383309887135065610560764003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255539924756710407040509335 383309887135065610560764003)
          ·
            refine ⟨574964830702598415841146005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383309887135065610560764003 574964830702598415841146005)
            ·
              refine ⟨26951476439184300742553719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 574964830702598415841146005 26951476439184300742553719)
              ·
                refine ⟨40427214658776451113830579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26951476439184300742553719 40427214658776451113830579)
                ·
                  refine ⟨60640821988164676670745869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40427214658776451113830579 60640821988164676670745869)
                  ·
                    refine ⟨22740308245561753751529701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60640821988164676670745869 22740308245561753751529701)
                    ·
                      refine ⟨4263807796042828828411819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22740308245561753751529701 4263807796042828828411819)
                      ·
                        rfl

theorem cell23_8303736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_8303736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303736 prefixEnd_8303736 := by exact prefixLift 8303736
  have htrace : WordTrace (prefixWord ++ tailWord_8303736) baseStart_8303736 baseEnd_8303736 := by
    simpa [prefixWord, tailWord_8303736, baseEnd_8303736] using wordTrace_append hprefix tailTrace_8303736
  have hstable : (prefixWord ++ tailWord_8303736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303736).length < 2 ^ (prefixWord ++ tailWord_8303736).sum := by decide
  have hdescent : baseEnd_8303736 < baseStart_8303736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303737 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 5]
def baseStart_8303737 : Nat := 118140960795 + 8303737 * 2 ^ 59
def prefixEnd_8303737 : Nat := 4983230072969 + 3 ^ 40 * 8303737 * 2
def baseEnd_8303737 : Nat := 473756478835942591611035

theorem tailTrace_8303737 : CollatzResearch.WordTrace tailWord_8303737 prefixEnd_8303737 473756478835942591611035 := by
  unfold tailWord_8303737
  simp only [CollatzResearch.WordTrace]
  refine ⟨302862169517986489218797465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201908113011990992812531643 302862169517986489218797465)
  ·
    refine ⟨227146627138489866914098099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302862169517986489218797465 227146627138489866914098099)
    ·
      refine ⟨340719940707734800371147149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227146627138489866914098099 340719940707734800371147149)
      ·
        refine ⟨127769977765400550139180181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340719940707734800371147149 127769977765400550139180181)
        ·
          refine ⟨5989217707753150787774071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127769977765400550139180181 5989217707753150787774071)
          ·
            refine ⟨8983826561629726181661107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989217707753150787774071 8983826561629726181661107)
            ·
              refine ⟨13475739842444589272491661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983826561629726181661107 13475739842444589272491661)
              ·
                refine ⟨5053402440916720977184373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13475739842444589272491661 5053402440916720977184373)
                ·
                  refine ⟨473756478835942591611035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053402440916720977184373 473756478835942591611035)
                  ·
                    rfl

theorem cell23_8303737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 5].length) (baseStart_8303737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303737 prefixEnd_8303737 := by exact prefixLift 8303737
  have htrace : WordTrace (prefixWord ++ tailWord_8303737) baseStart_8303737 baseEnd_8303737 := by
    simpa [prefixWord, tailWord_8303737, baseEnd_8303737] using wordTrace_append hprefix tailTrace_8303737
  have hstable : (prefixWord ++ tailWord_8303737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303737).length < 2 ^ (prefixWord ++ tailWord_8303737).sum := by decide
  have hdescent : baseEnd_8303737 < baseStart_8303737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303753 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_8303753 : Nat := 118140960795 + 8303753 * 2 ^ 59
def prefixEnd_8303753 : Nat := 4983230072969 + 3 ^ 40 * 8303753 * 2
def baseEnd_8303753 : Nat := 4263816525213955261899241

theorem tailTrace_8303753 : CollatzResearch.WordTrace tailWord_8303753 prefixEnd_8303753 4263816525213955261899241 := by
  unfold tailWord_8303753
  simp only [CollatzResearch.WordTrace]
  refine ⟨302862753085928523951379913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201908502057285682634253275 302862753085928523951379913)
  ·
    refine ⟨227147064814446392963534935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302862753085928523951379913 227147064814446392963534935)
    ·
      refine ⟨340720597221669589445302403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227147064814446392963534935 340720597221669589445302403)
      ·
        refine ⟨511080895832504384167953605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340720597221669589445302403 511080895832504384167953605)
        ·
          refine ⟨95827667968594572031491301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511080895832504384167953605 95827667968594572031491301)
          ·
            refine ⟨17967687744111482255904619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95827667968594572031491301 17967687744111482255904619)
            ·
              refine ⟨26951531616167223383856929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17967687744111482255904619 26951531616167223383856929)
              ·
                refine ⟨20213648712125417537892697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26951531616167223383856929 20213648712125417537892697)
                ·
                  refine ⟨15160236534094063153419523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20213648712125417537892697 15160236534094063153419523)
                  ·
                    refine ⟨22740354801141094730129285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15160236534094063153419523 22740354801141094730129285)
                    ·
                      refine ⟨4263816525213955261899241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22740354801141094730129285 4263816525213955261899241)
                      ·
                        rfl

theorem cell23_8303753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_8303753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303753 prefixEnd_8303753 := by exact prefixLift 8303753
  have htrace : WordTrace (prefixWord ++ tailWord_8303753) baseStart_8303753 baseEnd_8303753 := by
    simpa [prefixWord, tailWord_8303753, baseEnd_8303753] using wordTrace_append hprefix tailTrace_8303753
  have hstable : (prefixWord ++ tailWord_8303753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303753).length < 2 ^ (prefixWord ++ tailWord_8303753).sum := by decide
  have hdescent : baseEnd_8303753 < baseStart_8303753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303763 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 3, 4]
def baseStart_8303763 : Nat := 118140960795 + 8303763 * 2 ^ 59
def prefixEnd_8303763 : Nat := 4983230072969 + 3 ^ 40 * 8303763 * 2
def baseEnd_8303763 : Nat := 1421273886673500074258065

theorem tailTrace_8303763 : CollatzResearch.WordTrace tailWord_8303763 prefixEnd_8303763 1421273886673500074258065 := by
  unfold tailWord_8303763
  simp only [CollatzResearch.WordTrace]
  refine ⟨302863117815892295659243943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201908745210594863772829295 302863117815892295659243943)
  ·
    refine ⟨454294676723838443488865915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302863117815892295659243943 454294676723838443488865915)
    ·
      refine ⟨681442015085757665233298873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454294676723838443488865915 681442015085757665233298873)
      ·
        refine ⟨511081511314318248924974155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681442015085757665233298873 511081511314318248924974155)
        ·
          refine ⟨766622266971477373387461233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511081511314318248924974155 766622266971477373387461233)
          ·
            refine ⟨574966700228608030040595925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766622266971477373387461233 574966700228608030040595925)
            ·
              refine ⟨13475782036608000704076467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 574966700228608030040595925 13475782036608000704076467)
              ·
                refine ⟨20213673054912001056114701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475782036608000704076467 20213673054912001056114701)
                ·
                  refine ⟨7580127395592000396043013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20213673054912001056114701 7580127395592000396043013)
                  ·
                    refine ⟨1421273886673500074258065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580127395592000396043013 1421273886673500074258065)
                    ·
                      rfl

theorem cell23_8303763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 4].length) (baseStart_8303763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303763 prefixEnd_8303763 := by exact prefixLift 8303763
  have htrace : WordTrace (prefixWord ++ tailWord_8303763) baseStart_8303763 baseEnd_8303763 := by
    simpa [prefixWord, tailWord_8303763, baseEnd_8303763] using wordTrace_append hprefix tailTrace_8303763
  have hstable : (prefixWord ++ tailWord_8303763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303763).length < 2 ^ (prefixWord ++ tailWord_8303763).sum := by decide
  have hdescent : baseEnd_8303763 < baseStart_8303763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303773 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_8303773 : Nat := 118140960795 + 8303773 * 2 ^ 59
def prefixEnd_8303773 : Nat := 4983230072969 + 3 ^ 40 * 8303773 * 2
def baseEnd_8303773 : Nat := 4263826794827045183649149

theorem tailTrace_8303773 : CollatzResearch.WordTrace tailWord_8303773 prefixEnd_8303773 4263826794827045183649149 := by
  unfold tailWord_8303773
  simp only [CollatzResearch.WordTrace]
  refine ⟨302863482545856067367107973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201908988363904044911405315 302863482545856067367107973)
  ·
    refine ⟨56786902977348012631332745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302863482545856067367107973 56786902977348012631332745)
    ·
      refine ⟨42590177233011009473499559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56786902977348012631332745 42590177233011009473499559)
      ·
        refine ⟨63885265849516514210249339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42590177233011009473499559 63885265849516514210249339)
        ·
          refine ⟨95827898774274771315374009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63885265849516514210249339 95827898774274771315374009)
          ·
            refine ⟨71870924080706078486530507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95827898774274771315374009 71870924080706078486530507)
            ·
              refine ⟨107806386121059117729795761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71870924080706078486530507 107806386121059117729795761)
              ·
                refine ⟨80854789590794338297346821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107806386121059117729795761 80854789590794338297346821)
                ·
                  refine ⟨15160273048273938430752529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80854789590794338297346821 15160273048273938430752529)
                  ·
                    refine ⟨11370204786205453823064397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15160273048273938430752529 11370204786205453823064397)
                    ·
                      refine ⟨4263826794827045183649149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11370204786205453823064397 4263826794827045183649149)
                      ·
                        rfl

theorem cell23_8303773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_8303773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303773 prefixEnd_8303773 := by exact prefixLift 8303773
  have htrace : WordTrace (prefixWord ++ tailWord_8303773) baseStart_8303773 baseEnd_8303773 := by
    simpa [prefixWord, tailWord_8303773, baseEnd_8303773] using wordTrace_append hprefix tailTrace_8303773
  have hstable : (prefixWord ++ tailWord_8303773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303773).length < 2 ^ (prefixWord ++ tailWord_8303773).sum := by decide
  have hdescent : baseEnd_8303773 < baseStart_8303773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303803 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 3]
def baseStart_8303803 : Nat := 118140960795 + 8303803 * 2 ^ 59
def prefixEnd_8303803 : Nat := 4983230072969 + 3 ^ 40 * 8303803 * 2
def baseEnd_8303803 : Nat := 4263842199246680066274011

theorem tailTrace_8303803 : CollatzResearch.WordTrace tailWord_8303803 prefixEnd_8303803 4263842199246680066274011 := by
  unfold tailWord_8303803
  simp only [CollatzResearch.WordTrace]
  refine ⟨302864576735747382490700063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201909717823831588327133375 302864576735747382490700063)
  ·
    refine ⟨454296865103621073736050095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302864576735747382490700063 454296865103621073736050095)
    ·
      refine ⟨681445297655431610604075143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454296865103621073736050095 681445297655431610604075143)
      ·
        refine ⟨1022167946483147415906112715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681445297655431610604075143 1022167946483147415906112715)
        ·
          refine ⟨1533251919724721123859169073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022167946483147415906112715 1533251919724721123859169073)
          ·
            refine ⟨1149938939793540842894376805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533251919724721123859169073 1149938939793540842894376805)
            ·
              refine ⟨215613551211288908042695651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1149938939793540842894376805 215613551211288908042695651)
              ·
                refine ⟨323420326816933362064043477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215613551211288908042695651 323420326816933362064043477)
                ·
                  refine ⟨7580163909771875673376019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 323420326816933362064043477 7580163909771875673376019)
                  ·
                    refine ⟨11370245864657813510064029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580163909771875673376019 11370245864657813510064029)
                    ·
                      refine ⟨4263842199246680066274011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11370245864657813510064029 4263842199246680066274011)
                      ·
                        rfl

theorem cell23_8303803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 1, 3].length) (baseStart_8303803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303803 prefixEnd_8303803 := by exact prefixLift 8303803
  have htrace : WordTrace (prefixWord ++ tailWord_8303803) baseStart_8303803 baseEnd_8303803 := by
    simpa [prefixWord, tailWord_8303803, baseEnd_8303803] using wordTrace_append hprefix tailTrace_8303803
  have hstable : (prefixWord ++ tailWord_8303803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303803).length < 2 ^ (prefixWord ++ tailWord_8303803).sum := by decide
  have hdescent : baseEnd_8303803 < baseStart_8303803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303813 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 5, 2]
def baseStart_8303813 : Nat := 118140960795 + 8303813 * 2 ^ 59
def prefixEnd_8303813 : Nat := 4983230072969 + 3 ^ 40 * 8303813 * 2
def baseEnd_8303813 : Nat := 4263847334053225027148965

theorem tailTrace_8303813 : CollatzResearch.WordTrace tailWord_8303813 prefixEnd_8303813 4263847334053225027148965 := by
  unfold tailWord_8303813
  simp only [CollatzResearch.WordTrace]
  refine ⟨302864941465711154198564093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201909960977140769465709395 302864941465711154198564093)
  ·
    refine ⟨113574353049641682824461535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302864941465711154198564093 113574353049641682824461535)
    ·
      refine ⟨170361529574462524236692303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113574353049641682824461535 170361529574462524236692303)
      ·
        refine ⟨255542294361693786355038455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170361529574462524236692303 255542294361693786355038455)
        ·
          refine ⟨383313441542540679532557683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255542294361693786355038455 383313441542540679532557683)
          ·
            refine ⟨574970162313811019298836525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383313441542540679532557683 574970162313811019298836525)
            ·
              refine ⟨215613810867679132237063697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574970162313811019298836525 215613810867679132237063697)
              ·
                refine ⟨161710358150759349177797773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215613810867679132237063697 161710358150759349177797773)
                ·
                  refine ⟨60641384306534755941674165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161710358150759349177797773 60641384306534755941674165)
                  ·
                    refine ⟨5685129778737633369531953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60641384306534755941674165 5685129778737633369531953)
                    ·
                      refine ⟨4263847334053225027148965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685129778737633369531953 4263847334053225027148965)
                      ·
                        rfl

theorem cell23_8303813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_8303813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303813 prefixEnd_8303813 := by exact prefixLift 8303813
  have htrace : WordTrace (prefixWord ++ tailWord_8303813) baseStart_8303813 baseEnd_8303813 := by
    simpa [prefixWord, tailWord_8303813, baseEnd_8303813] using wordTrace_append hprefix tailTrace_8303813
  have hstable : (prefixWord ++ tailWord_8303813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303813).length < 2 ^ (prefixWord ++ tailWord_8303813).sum := by decide
  have hdescent : baseEnd_8303813 < baseStart_8303813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303847 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_8303847 : Nat := 118140960795 + 8303847 * 2 ^ 59
def prefixEnd_8303847 : Nat := 4983230072969 + 3 ^ 40 * 8303847 * 2
def baseEnd_8303847 : Nat := 4263864792395477894123809

theorem tailTrace_8303847 : CollatzResearch.WordTrace tailWord_8303847 prefixEnd_8303847 4263864792395477894123809 := by
  unfold tailWord_8303847
  simp only [CollatzResearch.WordTrace]
  refine ⟨302866181547587978005301795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201910787698391985336867863 302866181547587978005301795)
  ·
    refine ⟨454299272321381967007952693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302866181547587978005301795 454299272321381967007952693)
    ·
      refine ⟨42590556780129559406995565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454299272321381967007952693 42590556780129559406995565)
      ·
        refine ⟨15971458792548584777623337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42590556780129559406995565 15971458792548584777623337)
        ·
          refine ⟨11978594094411438583217503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971458792548584777623337 11978594094411438583217503)
          ·
            refine ⟨17967891141617157874826255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978594094411438583217503 17967891141617157874826255)
            ·
              refine ⟨26951836712425736812239383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17967891141617157874826255 26951836712425736812239383)
              ·
                refine ⟨40427755068638605218359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26951836712425736812239383 40427755068638605218359075)
                ·
                  refine ⟨60641632602957907827538613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40427755068638605218359075 60641632602957907827538613)
                  ·
                    refine ⟨5685153056527303858831745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60641632602957907827538613 5685153056527303858831745)
                    ·
                      refine ⟨4263864792395477894123809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685153056527303858831745 4263864792395477894123809)
                      ·
                        rfl

theorem cell23_8303847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_8303847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303847 prefixEnd_8303847 := by exact prefixLift 8303847
  have htrace : WordTrace (prefixWord ++ tailWord_8303847) baseStart_8303847 baseEnd_8303847 := by
    simpa [prefixWord, tailWord_8303847, baseEnd_8303847] using wordTrace_append hprefix tailTrace_8303847
  have hstable : (prefixWord ++ tailWord_8303847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303847).length < 2 ^ (prefixWord ++ tailWord_8303847).sum := by decide
  have hdescent : baseEnd_8303847 < baseStart_8303847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303856 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_8303856 : Nat := 118140960795 + 8303856 * 2 ^ 59
def prefixEnd_8303856 : Nat := 4983230072969 + 3 ^ 40 * 8303856 * 2
def baseEnd_8303856 : Nat := 4263869413721368358911267

theorem tailTrace_8303856 : CollatzResearch.WordTrace tailWord_8303856 prefixEnd_8303856 4263869413721368358911267 := by
  unfold tailWord_8303856
  simp only [CollatzResearch.WordTrace]
  refine ⟨151433254902277686271189711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201911006536370248361586281 151433254902277686271189711)
  ·
    refine ⟨227149882353416529406784567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151433254902277686271189711 227149882353416529406784567)
    ·
      refine ⟨340724823530124794110176851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227149882353416529406784567 340724823530124794110176851)
      ·
        refine ⟨511087235295187191165265277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340724823530124794110176851 511087235295187191165265277)
        ·
          refine ⟨191657713235695196686974479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511087235295187191165265277 191657713235695196686974479)
          ·
            refine ⟨287486569853542795030461719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191657713235695196686974479 287486569853542795030461719)
            ·
              refine ⟨431229854780314192545692579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287486569853542795030461719 431229854780314192545692579)
              ·
                refine ⟨646844782170471288818538869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431229854780314192545692579 646844782170471288818538869)
                ·
                  refine ⟨60641698328481683326738019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 646844782170471288818538869 60641698328481683326738019)
                  ·
                    refine ⟨90962547492722524990107029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60641698328481683326738019 90962547492722524990107029)
                    ·
                      refine ⟨4263869413721368358911267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90962547492722524990107029 4263869413721368358911267)
                      ·
                        rfl

theorem cell23_8303856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_8303856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303856 prefixEnd_8303856 := by exact prefixLift 8303856
  have htrace : WordTrace (prefixWord ++ tailWord_8303856) baseStart_8303856 baseEnd_8303856 := by
    simpa [prefixWord, tailWord_8303856, baseEnd_8303856] using wordTrace_append hprefix tailTrace_8303856
  have hstable : (prefixWord ++ tailWord_8303856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303856).length < 2 ^ (prefixWord ++ tailWord_8303856).sum := by decide
  have hdescent : baseEnd_8303856 < baseStart_8303856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303866 : List Nat := [3, 1, 1, 1, 1, 4, 12]
def baseStart_8303866 : Nat := 118140960795 + 8303866 * 2 ^ 59
def prefixEnd_8303866 : Nat := 4983230072969 + 3 ^ 40 * 8303866 * 2
def baseEnd_8303866 : Nat := 52640426525035966910941

theorem tailTrace_8303866 : CollatzResearch.WordTrace tailWord_8303866 prefixEnd_8303866 52640426525035966910941 := by
  unfold tailWord_8303866
  simp only [CollatzResearch.WordTrace]
  refine ⟨75716718633629786062560863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201911249689679429500162301 75716718633629786062560863)
  ·
    refine ⟨113575077950444679093841295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75716718633629786062560863 113575077950444679093841295)
    ·
      refine ⟨170362616925667018640761943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113575077950444679093841295 170362616925667018640761943)
      ·
        refine ⟨255543925388500527961142915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170362616925667018640761943 255543925388500527961142915)
        ·
          refine ⟨383315888082750791941714373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255543925388500527961142915 383315888082750791941714373)
          ·
            refine ⟨71871729015515773489071445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383315888082750791941714373 71871729015515773489071445)
            ·
              refine ⟨52640426525035966910941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71871729015515773489071445 52640426525035966910941)
              ·
                rfl

theorem cell23_8303866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 12].length) (baseStart_8303866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303866 prefixEnd_8303866 := by exact prefixLift 8303866
  have htrace : WordTrace (prefixWord ++ tailWord_8303866) baseStart_8303866 baseEnd_8303866 := by
    simpa [prefixWord, tailWord_8303866, baseEnd_8303866] using wordTrace_append hprefix tailTrace_8303866
  have hstable : (prefixWord ++ tailWord_8303866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303866).length < 2 ^ (prefixWord ++ tailWord_8303866).sum := by decide
  have hdescent : baseEnd_8303866 < baseStart_8303866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303877 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 3, 2, 2]
def baseStart_8303877 : Nat := 118140960795 + 8303877 * 2 ^ 59
def prefixEnd_8303877 : Nat := 4983230072969 + 3 ^ 40 * 8303877 * 2
def baseEnd_8303877 : Nat := 4263880196815112776748671

theorem tailTrace_8303877 : CollatzResearch.WordTrace tailWord_8303877 prefixEnd_8303877 4263880196815112776748671 := by
  unfold tailWord_8303877
  simp only [CollatzResearch.WordTrace]
  refine ⟨302867275737479293128893885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201911517158319528752595923 302867275737479293128893885)
  ·
    refine ⟨113575228401554734923335207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302867275737479293128893885 113575228401554734923335207)
    ·
      refine ⟨170362842602332102385002811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113575228401554734923335207 170362842602332102385002811)
      ·
        refine ⟨255544263903498153577504217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170362842602332102385002811 255544263903498153577504217)
        ·
          refine ⟨191658197927623615183128163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255544263903498153577504217 191658197927623615183128163)
          ·
            refine ⟨287487296891435422774692245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191658197927623615183128163 287487296891435422774692245)
            ·
              refine ⟨13475967041786035442563699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287487296891435422774692245 13475967041786035442563699)
              ·
                refine ⟨20213950562679053163845549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475967041786035442563699 20213950562679053163845549)
                ·
                  refine ⟨7580231461004644936442081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20213950562679053163845549 7580231461004644936442081)
                  ·
                    refine ⟨5685173595753483702331561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7580231461004644936442081 5685173595753483702331561)
                    ·
                      refine ⟨4263880196815112776748671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685173595753483702331561 4263880196815112776748671)
                      ·
                        rfl

theorem cell23_8303877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_8303877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303877 prefixEnd_8303877 := by exact prefixLift 8303877
  have htrace : WordTrace (prefixWord ++ tailWord_8303877) baseStart_8303877 baseEnd_8303877 := by
    simpa [prefixWord, tailWord_8303877, baseEnd_8303877] using wordTrace_append hprefix tailTrace_8303877
  have hstable : (prefixWord ++ tailWord_8303877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303877).length < 2 ^ (prefixWord ++ tailWord_8303877).sum := by decide
  have hdescent : baseEnd_8303877 < baseStart_8303877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303880 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_8303880 : Nat := 118140960795 + 8303880 * 2 ^ 59
def prefixEnd_8303880 : Nat := 4983230072969 + 3 ^ 40 * 8303880 * 2
def baseEnd_8303880 : Nat := 4263881737257076265011157

theorem tailTrace_8303880 : CollatzResearch.WordTrace tailWord_8303880 prefixEnd_8303880 4263881737257076265011157 := by
  unfold tailWord_8303880
  simp only [CollatzResearch.WordTrace]
  refine ⟨151433692578234212320626547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201911590104312283094168729 151433692578234212320626547)
  ·
    refine ⟨227150538867351318480939821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151433692578234212320626547 227150538867351318480939821)
    ·
      refine ⟨85181452075256744430352433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227150538867351318480939821 85181452075256744430352433)
      ·
        refine ⟨63886089056442558322764325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85181452075256744430352433 63886089056442558322764325)
        ·
          refine ⟨11978641698082979685518311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63886089056442558322764325 11978641698082979685518311)
          ·
            refine ⟨17967962547124469528277467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978641698082979685518311 17967962547124469528277467)
            ·
              refine ⟨26951943820686704292416201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17967962547124469528277467 26951943820686704292416201)
              ·
                refine ⟨20213957865515028219312151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26951943820686704292416201 20213957865515028219312151)
                ·
                  refine ⟨30320936798272542328968227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20213957865515028219312151 30320936798272542328968227)
                  ·
                    refine ⟨45481405197408813493452341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30320936798272542328968227 45481405197408813493452341)
                    ·
                      refine ⟨4263881737257076265011157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45481405197408813493452341 4263881737257076265011157)
                      ·
                        rfl

theorem cell23_8303880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_8303880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303880 prefixEnd_8303880 := by exact prefixLift 8303880
  have htrace : WordTrace (prefixWord ++ tailWord_8303880) baseStart_8303880 baseEnd_8303880 := by
    simpa [prefixWord, tailWord_8303880, baseEnd_8303880] using wordTrace_append hprefix tailTrace_8303880
  have hstable : (prefixWord ++ tailWord_8303880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303880).length < 2 ^ (prefixWord ++ tailWord_8303880).sum := by decide
  have hdescent : baseEnd_8303880 < baseStart_8303880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303953 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_8303953 : Nat := 118140960795 + 8303953 * 2 ^ 59
def prefixEnd_8303953 : Nat := 4983230072969 + 3 ^ 40 * 8303953 * 2
def baseEnd_8303953 : Nat := 4263919221344854479398321

theorem tailTrace_8303953 : CollatzResearch.WordTrace tailWord_8303953 prefixEnd_8303953 4263919221344854479398321 := by
  unfold tailWord_8303953
  simp only [CollatzResearch.WordTrace]
  refine ⟨302870047685203958108660513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201913365123469305405773675 302870047685203958108660513)
  ·
    refine ⟨227152535763902968581495385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302870047685203958108660513 227152535763902968581495385)
    ·
      refine ⟨170364401822927226436121539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227152535763902968581495385 170364401822927226436121539)
      ·
        refine ⟨255546602734390839654182309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170364401822927226436121539 255546602734390839654182309)
        ·
          refine ⟨47914988012698282435159183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255546602734390839654182309 47914988012698282435159183)
          ·
            refine ⟨71872482019047423652738775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47914988012698282435159183 71872482019047423652738775)
            ·
              refine ⟨107808723028571135479108163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71872482019047423652738775 107808723028571135479108163)
              ·
                refine ⟨161713084542856703218662245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107808723028571135479108163 161713084542856703218662245)
                ·
                  refine ⟨30321203351785631853499171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161713084542856703218662245 30321203351785631853499171)
                  ·
                    refine ⟨45481805027678447780248757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30321203351785631853499171 45481805027678447780248757)
                    ·
                      refine ⟨4263919221344854479398321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45481805027678447780248757 4263919221344854479398321)
                      ·
                        rfl

theorem cell23_8303953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_8303953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303953 prefixEnd_8303953 := by exact prefixLift 8303953
  have htrace : WordTrace (prefixWord ++ tailWord_8303953) baseStart_8303953 baseEnd_8303953 := by
    simpa [prefixWord, tailWord_8303953, baseEnd_8303953] using wordTrace_append hprefix tailTrace_8303953
  have hstable : (prefixWord ++ tailWord_8303953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303953).length < 2 ^ (prefixWord ++ tailWord_8303953).sum := by decide
  have hdescent : baseEnd_8303953 < baseStart_8303953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303970 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_8303970 : Nat := 118140960795 + 8303970 * 2 ^ 59
def prefixEnd_8303970 : Nat := 4983230072969 + 3 ^ 40 * 8303970 * 2
def baseEnd_8303970 : Nat := 4263927950515980912885743

theorem tailTrace_8303970 : CollatzResearch.WordTrace tailWord_8303970 prefixEnd_8303970 4263927950515980912885743 := by
  unfold tailWord_8303970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75717666931535592503007341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201913778484094913341352909 75717666931535592503007341)
  ·
    refine ⟨28394125099325847188627753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75717666931535592503007341 28394125099325847188627753)
    ·
      refine ⟨21295593824494385391470815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28394125099325847188627753 21295593824494385391470815)
      ·
        refine ⟨31943390736741578087206223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21295593824494385391470815 31943390736741578087206223)
        ·
          refine ⟨47915086105112367130809335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31943390736741578087206223 47915086105112367130809335)
          ·
            refine ⟨71872629157668550696214003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47915086105112367130809335 71872629157668550696214003)
            ·
              refine ⟨107808943736502826044321005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71872629157668550696214003 107808943736502826044321005)
              ·
                refine ⟨40428353901188559766620377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107808943736502826044321005 40428353901188559766620377)
                ·
                  refine ⟨30321265425891419824965283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40428353901188559766620377 30321265425891419824965283)
                  ·
                    refine ⟨45481898138837129737447925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30321265425891419824965283 45481898138837129737447925)
                    ·
                      refine ⟨4263927950515980912885743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45481898138837129737447925 4263927950515980912885743)
                      ·
                        rfl

theorem cell23_8303970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_8303970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303970 prefixEnd_8303970 := by exact prefixLift 8303970
  have htrace : WordTrace (prefixWord ++ tailWord_8303970) baseStart_8303970 baseEnd_8303970 := by
    simpa [prefixWord, tailWord_8303970, baseEnd_8303970] using wordTrace_append hprefix tailTrace_8303970
  have hstable : (prefixWord ++ tailWord_8303970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303970).length < 2 ^ (prefixWord ++ tailWord_8303970).sum := by decide
  have hdescent : baseEnd_8303970 < baseStart_8303970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8303984 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2]
def baseStart_8303984 : Nat := 118140960795 + 8303984 * 2 ^ 59
def prefixEnd_8303984 : Nat := 4983230072969 + 3 ^ 40 * 8303984 * 2
def baseEnd_8303984 : Nat := 4263935139245143858110679

theorem tailTrace_8303984 : CollatzResearch.WordTrace tailWord_8303984 prefixEnd_8303984 4263935139245143858110679 := by
  unfold tailWord_8303984
  simp only [CollatzResearch.WordTrace]
  refine ⟨151435589174045825201519503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201914118898727766935359337 151435589174045825201519503)
  ·
    refine ⟨227153383761068737802279255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151435589174045825201519503 227153383761068737802279255)
    ·
      refine ⟨340730075641603106703418883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227153383761068737802279255 340730075641603106703418883)
      ·
        refine ⟨511095113462404660055128325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340730075641603106703418883 511095113462404660055128325)
        ·
          refine ⟨95830333774200873760336561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 511095113462404660055128325 95830333774200873760336561)
          ·
            refine ⟨71872750330650655320252421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95830333774200873760336561 71872750330650655320252421)
            ·
              refine ⟨13476140686996997872547329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71872750330650655320252421 13476140686996997872547329)
              ·
                refine ⟨10107105515247748404410497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13476140686996997872547329 10107105515247748404410497)
                ·
                  refine ⟨7580329136435811303307873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10107105515247748404410497 7580329136435811303307873)
                  ·
                    refine ⟨5685246852326858477480905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7580329136435811303307873 5685246852326858477480905)
                    ·
                      refine ⟨4263935139245143858110679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685246852326858477480905 4263935139245143858110679)
                      ·
                        rfl

theorem cell23_8303984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2].length) (baseStart_8303984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8303984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8303984 prefixEnd_8303984 := by exact prefixLift 8303984
  have htrace : WordTrace (prefixWord ++ tailWord_8303984) baseStart_8303984 baseEnd_8303984 := by
    simpa [prefixWord, tailWord_8303984, baseEnd_8303984] using wordTrace_append hprefix tailTrace_8303984
  have hstable : (prefixWord ++ tailWord_8303984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8303984).length < 2 ^ (prefixWord ++ tailWord_8303984).sum := by decide
  have hdescent : baseEnd_8303984 < baseStart_8303984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8303984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304024 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 5]
def baseStart_8304024 : Nat := 118140960795 + 8304024 * 2 ^ 59
def prefixEnd_8304024 : Nat := 4983230072969 + 3 ^ 40 * 8304024 * 2
def baseEnd_8304024 : Nat := 473772853163480411290055

theorem tailTrace_8304024 : CollatzResearch.WordTrace tailWord_8304024 prefixEnd_8304024 473772853163480411290055 := by
  unfold tailWord_8304024
  simp only [CollatzResearch.WordTrace]
  refine ⟨151436318633973368617247563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201915091511964491489663417 151436318633973368617247563)
  ·
    refine ⟨227154477950960052925871345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151436318633973368617247563 227154477950960052925871345)
    ·
      refine ⟨170365858463220039694403509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227154477950960052925871345 170365858463220039694403509)
      ·
        refine ⟨15971799230926878721350329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170365858463220039694403509 15971799230926878721350329)
        ·
          refine ⟨11978849423195159041012747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971799230926878721350329 11978849423195159041012747)
          ·
            refine ⟨17968274134792738561519121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978849423195159041012747 17968274134792738561519121)
            ·
              refine ⟨13476205601094553921139341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17968274134792738561519121 13476205601094553921139341)
              ·
                refine ⟨5053577100410457720427253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13476205601094553921139341 5053577100410457720427253)
                ·
                  refine ⟨473772853163480411290055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053577100410457720427253 473772853163480411290055)
                  ·
                    rfl

theorem cell23_8304024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 5].length) (baseStart_8304024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304024 prefixEnd_8304024 := by exact prefixLift 8304024
  have htrace : WordTrace (prefixWord ++ tailWord_8304024) baseStart_8304024 baseEnd_8304024 := by
    simpa [prefixWord, tailWord_8304024, baseEnd_8304024] using wordTrace_append hprefix tailTrace_8304024
  have hstable : (prefixWord ++ tailWord_8304024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304024).length < 2 ^ (prefixWord ++ tailWord_8304024).sum := by decide
  have hdescent : baseEnd_8304024 < baseStart_8304024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304083 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_8304083 : Nat := 118140960795 + 8304083 * 2 ^ 59
def prefixEnd_8304083 : Nat := 4983230072969 + 3 ^ 40 * 8304083 * 2
def baseEnd_8304083 : Nat := 4263985973829938970772723

theorem tailTrace_8304083 : CollatzResearch.WordTrace tailWord_8304083 prefixEnd_8304083 4263985973829938970772723 := by
  unfold tailWord_8304083
  simp only [CollatzResearch.WordTrace]
  refine ⟨302874789174732990310892903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201916526116488660207261935 302874789174732990310892903)
  ·
    refine ⟨454312183762099485466339355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302874789174732990310892903 454312183762099485466339355)
    ·
      refine ⟨681468275643149228199509033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454312183762099485466339355 681468275643149228199509033)
      ·
        refine ⟨511101206732361921149631775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681468275643149228199509033 511101206732361921149631775)
        ·
          refine ⟨766651810098542881724447663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511101206732361921149631775 766651810098542881724447663)
          ·
            refine ⟨1149977715147814322586671495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766651810098542881724447663 1149977715147814322586671495)
            ·
              refine ⟨1724966572721721483880007243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149977715147814322586671495 1724966572721721483880007243)
              ·
                refine ⟨2587449859082582225820010865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724966572721721483880007243 2587449859082582225820010865)
                ·
                  refine ⟨1940587394311936669365008149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587449859082582225820010865 1940587394311936669365008149)
                  ·
                    refine ⟨90965034108372031376484757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1940587394311936669365008149 90965034108372031376484757)
                    ·
                      refine ⟨4263985973829938970772723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90965034108372031376484757 4263985973829938970772723)
                      ·
                        rfl

theorem cell23_8304083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_8304083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304083 prefixEnd_8304083 := by exact prefixLift 8304083
  have htrace : WordTrace (prefixWord ++ tailWord_8304083) baseStart_8304083 baseEnd_8304083 := by
    simpa [prefixWord, tailWord_8304083, baseEnd_8304083] using wordTrace_append hprefix tailTrace_8304083
  have hstable : (prefixWord ++ tailWord_8304083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304083).length < 2 ^ (prefixWord ++ tailWord_8304083).sum := by decide
  have hdescent : baseEnd_8304083 < baseStart_8304083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304107 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 3]
def baseStart_8304107 : Nat := 118140960795 + 8304107 * 2 ^ 59
def prefixEnd_8304107 : Nat := 4983230072969 + 3 ^ 40 * 8304107 * 2
def baseEnd_8304107 : Nat := 4263998297365646876872613

theorem tailTrace_8304107 : CollatzResearch.WordTrace tailWord_8304107 prefixEnd_8304107 4263998297365646876872613 := by
  unfold tailWord_8304107
  simp only [CollatzResearch.WordTrace]
  refine ⟨302875664526646042409766575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201917109684430694939844383 302875664526646042409766575)
  ·
    refine ⟨454313496789969063614649863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302875664526646042409766575 454313496789969063614649863)
    ·
      refine ⟨681470245184953595421974795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454313496789969063614649863 681470245184953595421974795)
      ·
        refine ⟨1022205367777430393132962193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681470245184953595421974795 1022205367777430393132962193)
        ·
          refine ⟨766654025833072794849721645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1022205367777430393132962193 766654025833072794849721645)
          ·
            refine ⟨287495259687402298068645617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766654025833072794849721645 287495259687402298068645617)
            ·
              refine ⟨215621444765551723551484213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287495259687402298068645617 215621444765551723551484213)
              ·
                refine ⟨20214510446770474082951645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215621444765551723551484213 20214510446770474082951645)
                ·
                  refine ⟨7580441417538927781106867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20214510446770474082951645 7580441417538927781106867)
                  ·
                    refine ⟨11370662126308391671660301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580441417538927781106867 11370662126308391671660301)
                    ·
                      refine ⟨4263998297365646876872613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11370662126308391671660301 4263998297365646876872613)
                      ·
                        rfl

theorem cell23_8304107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 1, 3].length) (baseStart_8304107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304107 prefixEnd_8304107 := by exact prefixLift 8304107
  have htrace : WordTrace (prefixWord ++ tailWord_8304107) baseStart_8304107 baseEnd_8304107 := by
    simpa [prefixWord, tailWord_8304107, baseEnd_8304107] using wordTrace_append hprefix tailTrace_8304107
  have hstable : (prefixWord ++ tailWord_8304107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304107).length < 2 ^ (prefixWord ++ tailWord_8304107).sum := by decide
  have hdescent : baseEnd_8304107 < baseStart_8304107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304114 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_8304114 : Nat := 118140960795 + 8304114 * 2 ^ 59
def prefixEnd_8304114 : Nat := 4983230072969 + 3 ^ 40 * 8304114 * 2
def baseEnd_8304114 : Nat := 473777987970025372165009

theorem tailTrace_8304114 : CollatzResearch.WordTrace tailWord_8304114 prefixEnd_8304114 473777987970025372165009 := by
  unfold tailWord_8304114
  simp only [CollatzResearch.WordTrace]
  refine ⟨75718979959405170651317849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201917279891747121736847597 75718979959405170651317849)
  ·
    refine ⟨56789234969553877988488387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75718979959405170651317849 56789234969553877988488387)
    ·
      refine ⟨85183852454330816982732581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56789234969553877988488387 85183852454330816982732581)
      ·
        refine ⟨15971972335187028184262359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85183852454330816982732581 15971972335187028184262359)
        ·
          refine ⟨23957958502780542276393539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15971972335187028184262359 23957958502780542276393539)
          ·
            refine ⟨35936937754170813414590309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23957958502780542276393539 35936937754170813414590309)
            ·
              refine ⟨6738175828907027515235683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35936937754170813414590309 6738175828907027515235683)
              ·
                refine ⟨10107263743360541272853525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738175828907027515235683 10107263743360541272853525)
                ·
                  refine ⟨473777987970025372165009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10107263743360541272853525 473777987970025372165009)
                  ·
                    rfl

theorem cell23_8304114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_8304114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304114 prefixEnd_8304114 := by exact prefixLift 8304114
  have htrace : WordTrace (prefixWord ++ tailWord_8304114) baseStart_8304114 baseEnd_8304114 := by
    simpa [prefixWord, tailWord_8304114, baseEnd_8304114] using wordTrace_append hprefix tailTrace_8304114
  have hstable : (prefixWord ++ tailWord_8304114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304114).length < 2 ^ (prefixWord ++ tailWord_8304114).sum := by decide
  have hdescent : baseEnd_8304114 < baseStart_8304114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304174 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_8304174 : Nat := 118140960795 + 8304174 * 2 ^ 59
def prefixEnd_8304174 : Nat := 4983230072969 + 3 ^ 40 * 8304174 * 2
def baseEnd_8304174 : Nat := 1421344233523166038244935

theorem tailTrace_8304174 : CollatzResearch.WordTrace tailWord_8304174 prefixEnd_8304174 1421344233523166038244935 := by
  unfold tailWord_8304174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37859763527175414106556947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201918738811602208568303717 37859763527175414106556947)
  ·
    refine ⟨56789645290763121159835421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37859763527175414106556947 56789645290763121159835421)
    ·
      refine ⟨21296116984036170434938283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56789645290763121159835421 21296116984036170434938283)
      ·
        refine ⟨31944175476054255652407425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21296116984036170434938283 31944175476054255652407425)
        ·
          refine ⟨23958131607040691739305569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31944175476054255652407425 23958131607040691739305569)
          ·
            refine ⟨17968598705280518804479177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23958131607040691739305569 17968598705280518804479177)
            ·
              refine ⟨13476449028960389103359383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17968598705280518804479177 13476449028960389103359383)
              ·
                refine ⟨20214673543440583655039075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13476449028960389103359383 20214673543440583655039075)
                ·
                  refine ⟨30322010315160875482558613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20214673543440583655039075 30322010315160875482558613)
                  ·
                    refine ⟨1421344233523166038244935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30322010315160875482558613 1421344233523166038244935)
                    ·
                      rfl

theorem cell23_8304174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_8304174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304174 prefixEnd_8304174 := by exact prefixLift 8304174
  have htrace : WordTrace (prefixWord ++ tailWord_8304174) baseStart_8304174 baseEnd_8304174 := by
    simpa [prefixWord, tailWord_8304174, baseEnd_8304174] using wordTrace_append hprefix tailTrace_8304174
  have hstable : (prefixWord ++ tailWord_8304174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304174).length < 2 ^ (prefixWord ++ tailWord_8304174).sum := by decide
  have hdescent : baseEnd_8304174 < baseStart_8304174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304181 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_8304181 : Nat := 118140960795 + 8304181 * 2 ^ 59
def prefixEnd_8304181 : Nat := 4983230072969 + 3 ^ 40 * 8304181 * 2
def baseEnd_8304181 : Nat := 4264036294934079587347273

theorem tailTrace_8304181 : CollatzResearch.WordTrace tailWord_8304181 prefixEnd_8304181 4264036294934079587347273 := by
  unfold tailWord_8304181
  simp only [CollatzResearch.WordTrace]
  refine ⟨302878363528377953047960397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201918909018918635365306931 302878363528377953047960397)
  ·
    refine ⟨113579386323141732392985149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302878363528377953047960397 113579386323141732392985149)
    ·
      refine ⟨42592269871178149647369431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113579386323141732392985149 42592269871178149647369431)
      ·
        refine ⟨63888404806767224471054147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42592269871178149647369431 63888404806767224471054147)
        ·
          refine ⟨95832607210150836706581221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63888404806767224471054147 95832607210150836706581221)
          ·
            refine ⟨17968613851903281882483979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95832607210150836706581221 17968613851903281882483979)
            ·
              refine ⟨26952920777854922823725969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17968613851903281882483979 26952920777854922823725969)
              ·
                refine ⟨20214690583391192117794477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26952920777854922823725969 20214690583391192117794477)
                ·
                  refine ⟨7580508968771697044172929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20214690583391192117794477 7580508968771697044172929)
                  ·
                    refine ⟨5685381726578772783129697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7580508968771697044172929 5685381726578772783129697)
                    ·
                      refine ⟨4264036294934079587347273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685381726578772783129697 4264036294934079587347273)
                      ·
                        rfl

theorem cell23_8304181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_8304181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304181 prefixEnd_8304181 := by exact prefixLift 8304181
  have htrace : WordTrace (prefixWord ++ tailWord_8304181) baseStart_8304181 baseEnd_8304181 := by
    simpa [prefixWord, tailWord_8304181, baseEnd_8304181] using wordTrace_append hprefix tailTrace_8304181
  have hstable : (prefixWord ++ tailWord_8304181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304181).length < 2 ^ (prefixWord ++ tailWord_8304181).sum := by decide
  have hdescent : baseEnd_8304181 < baseStart_8304181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304197 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 3]
def baseStart_8304197 : Nat := 118140960795 + 8304197 * 2 ^ 59
def prefixEnd_8304197 : Nat := 4983230072969 + 3 ^ 40 * 8304197 * 2
def baseEnd_8304197 : Nat := 4264044510624551524747199

theorem tailTrace_8304197 : CollatzResearch.WordTrace tailWord_8304197 prefixEnd_8304197 4264044510624551524747199 := by
  unfold tailWord_8304197
  simp only [CollatzResearch.WordTrace]
  refine ⟨302878947096319987780542845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201919298064213325187028563 302878947096319987780542845)
  ·
    refine ⟨113579605161119995417703567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302878947096319987780542845 113579605161119995417703567)
    ·
      refine ⟨170369407741679993126555351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113579605161119995417703567 170369407741679993126555351)
      ·
        refine ⟨255554111612519989689833027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170369407741679993126555351 255554111612519989689833027)
        ·
          refine ⟨383331167418779984534749541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255554111612519989689833027 383331167418779984534749541)
          ·
            refine ⟨71874593891021247100265539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383331167418779984534749541 71874593891021247100265539)
            ·
              refine ⟨107811890836531870650398309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71874593891021247100265539 107811890836531870650398309)
              ·
                refine ⟨20214729531849725746949683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107811890836531870650398309 20214729531849725746949683)
                ·
                  refine ⟨30322094297774588620424525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20214729531849725746949683 30322094297774588620424525)
                  ·
                    refine ⟨11370785361665470732659197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30322094297774588620424525 11370785361665470732659197)
                    ·
                      refine ⟨4264044510624551524747199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11370785361665470732659197 4264044510624551524747199)
                      ·
                        rfl

theorem cell23_8304197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_8304197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304197 prefixEnd_8304197 := by exact prefixLift 8304197
  have htrace : WordTrace (prefixWord ++ tailWord_8304197) baseStart_8304197 baseEnd_8304197 := by
    simpa [prefixWord, tailWord_8304197, baseEnd_8304197] using wordTrace_append hprefix tailTrace_8304197
  have hstable : (prefixWord ++ tailWord_8304197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304197).length < 2 ^ (prefixWord ++ tailWord_8304197).sum := by decide
  have hdescent : baseEnd_8304197 < baseStart_8304197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304198 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_8304198 : Nat := 118140960795 + 8304198 * 2 ^ 59
def prefixEnd_8304198 : Nat := 4983230072969 + 3 ^ 40 * 8304198 * 2
def baseEnd_8304198 : Nat := 4264045024105206020834695

theorem tailTrace_8304198 : CollatzResearch.WordTrace tailWord_8304198 prefixEnd_8304198 4264045024105206020834695 := by
  unfold tailWord_8304198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464968236541136404729039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201919322379544243300886165 9464968236541136404729039)
  ·
    refine ⟨14197452354811704607093559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9464968236541136404729039 14197452354811704607093559)
    ·
      refine ⟨21296178532217556910640339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14197452354811704607093559 21296178532217556910640339)
      ·
        refine ⟨31944267798326335365960509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21296178532217556910640339 31944267798326335365960509)
        ·
          refine ⟨11979100424372375762235191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31944267798326335365960509 11979100424372375762235191)
          ·
            refine ⟨17968650636558563643352787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979100424372375762235191 17968650636558563643352787)
            ·
              refine ⟨26952975954837845465029181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17968650636558563643352787 26952975954837845465029181)
              ·
                refine ⟨10107365983064192049385943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26952975954837845465029181 10107365983064192049385943)
                ·
                  refine ⟨15161048974596288074078915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10107365983064192049385943 15161048974596288074078915)
                  ·
                    refine ⟨22741573461894432111118373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15161048974596288074078915 22741573461894432111118373)
                    ·
                      refine ⟨4264045024105206020834695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22741573461894432111118373 4264045024105206020834695)
                      ·
                        rfl

theorem cell23_8304198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_8304198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304198 prefixEnd_8304198 := by exact prefixLift 8304198
  have htrace : WordTrace (prefixWord ++ tailWord_8304198) baseStart_8304198 baseEnd_8304198 := by
    simpa [prefixWord, tailWord_8304198, baseEnd_8304198] using wordTrace_append hprefix tailTrace_8304198
  have hstable : (prefixWord ++ tailWord_8304198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304198).length < 2 ^ (prefixWord ++ tailWord_8304198).sum := by decide
  have hdescent : baseEnd_8304198 < baseStart_8304198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304257 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_8304257 : Nat := 118140960795 + 8304257 * 2 ^ 59
def prefixEnd_8304257 : Nat := 4983230072969 + 3 ^ 40 * 8304257 * 2
def baseEnd_8304257 : Nat := 4264075319463821289996923

theorem tailTrace_8304257 : CollatzResearch.WordTrace tailWord_8304257 prefixEnd_8304257 4264075319463821289996923 := by
  unfold tailWord_8304257
  simp only [CollatzResearch.WordTrace]
  refine ⟨302881135476102618027727025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201920756984068412018484683 302881135476102618027727025)
  ·
    refine ⟨227160851607076963520795269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302881135476102618027727025 227160851607076963520795269)
    ·
      refine ⟨42592659676326930660149113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227160851607076963520795269 42592659676326930660149113)
      ·
        refine ⟨31944494757245197995111835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42592659676326930660149113 31944494757245197995111835)
        ·
          refine ⟨47916742135867796992667753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31944494757245197995111835 47916742135867796992667753)
          ·
            refine ⟨35937556601900847744500815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47916742135867796992667753 35937556601900847744500815)
            ·
              refine ⟨53906334902851271616751223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35937556601900847744500815 53906334902851271616751223)
              ·
                refine ⟨80859502354276907425126835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53906334902851271616751223 80859502354276907425126835)
                ·
                  refine ⟨121289253531415361137690253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80859502354276907425126835 121289253531415361137690253)
                  ·
                    refine ⟨45483470074280760426633845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121289253531415361137690253 45483470074280760426633845)
                    ·
                      refine ⟨4264075319463821289996923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45483470074280760426633845 4264075319463821289996923)
                      ·
                        rfl

theorem cell23_8304257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_8304257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304257 prefixEnd_8304257 := by exact prefixLift 8304257
  have htrace : WordTrace (prefixWord ++ tailWord_8304257) baseStart_8304257 baseEnd_8304257 := by
    simpa [prefixWord, tailWord_8304257, baseEnd_8304257] using wordTrace_append hprefix tailTrace_8304257
  have hstable : (prefixWord ++ tailWord_8304257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304257).length < 2 ^ (prefixWord ++ tailWord_8304257).sum := by decide
  have hdescent : baseEnd_8304257 < baseStart_8304257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304288 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2]
def baseStart_8304288 : Nat := 118140960795 + 8304288 * 2 ^ 59
def prefixEnd_8304288 : Nat := 4983230072969 + 3 ^ 40 * 8304288 * 2
def baseEnd_8304288 : Nat := 4264091237364110668709281

theorem tailTrace_8304288 : CollatzResearch.WordTrace tailWord_8304288 prefixEnd_8304288 4264091237364110668709281 := by
  unfold tailWord_8304288
  simp only [CollatzResearch.WordTrace]
  refine ⟨151441133069495155161052759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201921510759326873548070345 151441133069495155161052759)
  ·
    refine ⟨227161699604242732741579139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151441133069495155161052759 227161699604242732741579139)
    ·
      refine ⟨340742549406364099112368709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227161699604242732741579139 340742549406364099112368709)
      ·
        refine ⟨63889228013693268583569133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340742549406364099112368709 63889228013693268583569133)
        ·
          refine ⟨23958460505134975718838425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63889228013693268583569133 23958460505134975718838425)
          ·
            refine ⟨17968845378851231789128819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23958460505134975718838425 17968845378851231789128819)
            ·
              refine ⟨26953268068276847683693229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17968845378851231789128819 26953268068276847683693229)
              ·
                refine ⟨10107475525603817881384961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26953268068276847683693229 10107475525603817881384961)
                ·
                  refine ⟨7580606644202863411038721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10107475525603817881384961 7580606644202863411038721)
                  ·
                    refine ⟨5685454983152147558279041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7580606644202863411038721 5685454983152147558279041)
                    ·
                      refine ⟨4264091237364110668709281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685454983152147558279041 4264091237364110668709281)
                      ·
                        rfl

theorem cell23_8304288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_8304288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304288 prefixEnd_8304288 := by exact prefixLift 8304288
  have htrace : WordTrace (prefixWord ++ tailWord_8304288) baseStart_8304288 baseEnd_8304288 := by
    simpa [prefixWord, tailWord_8304288, baseEnd_8304288] using wordTrace_append hprefix tailTrace_8304288
  have hstable : (prefixWord ++ tailWord_8304288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304288).length < 2 ^ (prefixWord ++ tailWord_8304288).sum := by decide
  have hdescent : baseEnd_8304288 < baseStart_8304288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304317 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_8304317 : Nat := 118140960795 + 8304317 * 2 ^ 59
def prefixEnd_8304317 : Nat := 4983230072969 + 3 ^ 40 * 8304317 * 2
def baseEnd_8304317 : Nat := 4264106128303091055246647

theorem tailTrace_8304317 : CollatzResearch.WordTrace tailWord_8304317 prefixEnd_8304317 4264106128303091055246647 := by
  unfold tailWord_8304317
  simp only [CollatzResearch.WordTrace]
  refine ⟨302883323855885248274911205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201922215903923498849940803 302883323855885248274911205)
  ·
    refine ⟨56790623222978484051545851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302883323855885248274911205 56790623222978484051545851)
    ·
      refine ⟨85185934834467726077318777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56790623222978484051545851 85185934834467726077318777)
      ·
        refine ⟨63889451125850794557989083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85185934834467726077318777 63889451125850794557989083)
        ·
          refine ⟨95834176688776191836983625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63889451125850794557989083 95834176688776191836983625)
          ·
            refine ⟨71875632516582143877737719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95834176688776191836983625 71875632516582143877737719)
            ·
              refine ⟨107813448774873215816606579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71875632516582143877737719 107813448774873215816606579)
              ·
                refine ⟨161720173162309823724909869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107813448774873215816606579 161720173162309823724909869)
                ·
                  refine ⟨60645064935866183896841201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161720173162309823724909869 60645064935866183896841201)
                  ·
                    refine ⟨45483798701899637922630901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60645064935866183896841201 45483798701899637922630901)
                    ·
                      refine ⟨4264106128303091055246647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45483798701899637922630901 4264106128303091055246647)
                      ·
                        rfl

theorem cell23_8304317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_8304317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304317 prefixEnd_8304317 := by exact prefixLift 8304317
  have htrace : WordTrace (prefixWord ++ tailWord_8304317) baseStart_8304317 baseEnd_8304317 := by
    simpa [prefixWord, tailWord_8304317, baseEnd_8304317] using wordTrace_append hprefix tailTrace_8304317
  have hstable : (prefixWord ++ tailWord_8304317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304317).length < 2 ^ (prefixWord ++ tailWord_8304317).sum := by decide
  have hdescent : baseEnd_8304317 < baseStart_8304317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304324 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_8304324 : Nat := 118140960795 + 8304324 * 2 ^ 59
def prefixEnd_8304324 : Nat := 4983230072969 + 3 ^ 40 * 8304324 * 2
def baseEnd_8304324 : Nat := 1421369907555890842619705

theorem tailTrace_8304324 : CollatzResearch.WordTrace tailWord_8304324 prefixEnd_8304324 1421369907555890842619705 := by
  unfold tailWord_8304324
  simp only [CollatzResearch.WordTrace]
  refine ⟨151441789583429944235208013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201922386111239925646944017 151441789583429944235208013)
  ·
    refine ⟨56790671093786229088203005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151441789583429944235208013 56790671093786229088203005)
    ·
      refine ⟨21296501660169835908076127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56790671093786229088203005 21296501660169835908076127)
      ·
        refine ⟨31944752490254753862114191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21296501660169835908076127 31944752490254753862114191)
        ·
          refine ⟨47917128735382130793171287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31944752490254753862114191 47917128735382130793171287)
          ·
            refine ⟨71875693103073196189756931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47917128735382130793171287 71875693103073196189756931)
            ·
              refine ⟨107813539654609794284635397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71875693103073196189756931 107813539654609794284635397)
              ·
                refine ⟨20215038685239336428369137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107813539654609794284635397 20215038685239336428369137)
                ·
                  refine ⟨15161279013929502321276853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20215038685239336428369137 15161279013929502321276853)
                  ·
                    refine ⟨1421369907555890842619705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15161279013929502321276853 1421369907555890842619705)
                    ·
                      rfl

theorem cell23_8304324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_8304324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304324 prefixEnd_8304324 := by exact prefixLift 8304324
  have htrace : WordTrace (prefixWord ++ tailWord_8304324) baseStart_8304324 baseEnd_8304324 := by
    simpa [prefixWord, tailWord_8304324, baseEnd_8304324] using wordTrace_append hprefix tailTrace_8304324
  have hstable : (prefixWord ++ tailWord_8304324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304324).length < 2 ^ (prefixWord ++ tailWord_8304324).sum := by decide
  have hdescent : baseEnd_8304324 < baseStart_8304324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304367 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 8]
def baseStart_8304367 : Nat := 118140960795 + 8304367 * 2 ^ 59
def prefixEnd_8304367 : Nat := 4983230072969 + 3 ^ 40 * 8304367 * 2
def baseEnd_8304367 : Nat := 473792422481757317735713

theorem tailTrace_8304367 : CollatzResearch.WordTrace tailWord_8304367 prefixEnd_8304367 473792422481757317735713 := by
  unfold tailWord_8304367
  simp only [CollatzResearch.WordTrace]
  refine ⟨302885147505704106814231355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201923431670469404542820903 302885147505704106814231355)
  ·
    refine ⟨454327721258556160221347033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302885147505704106814231355 454327721258556160221347033)
    ·
      refine ⟨340745790943917120166010275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454327721258556160221347033 340745790943917120166010275)
      ·
        refine ⟨511118686415875680249015413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340745790943917120166010275 511118686415875680249015413)
        ·
          refine ⟨47917376851488345023345195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 511118686415875680249015413 47917376851488345023345195)
          ·
            refine ⟨71876065277232517535017793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47917376851488345023345195 71876065277232517535017793)
            ·
              refine ⟨53907048957924388151263345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71876065277232517535017793 53907048957924388151263345)
              ·
                refine ⟨40430286718443291113447509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53907048957924388151263345 40430286718443291113447509)
                ·
                  refine ⟨473792422481757317735713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40430286718443291113447509 473792422481757317735713)
                  ·
                    rfl

theorem cell23_8304367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 8].length) (baseStart_8304367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304367 prefixEnd_8304367 := by exact prefixLift 8304367
  have htrace : WordTrace (prefixWord ++ tailWord_8304367) baseStart_8304367 baseEnd_8304367 := by
    simpa [prefixWord, tailWord_8304367, baseEnd_8304367] using wordTrace_append hprefix tailTrace_8304367
  have hstable : (prefixWord ++ tailWord_8304367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304367).length < 2 ^ (prefixWord ++ tailWord_8304367).sum := by decide
  have hdescent : baseEnd_8304367 < baseStart_8304367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304371 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 1, 4]
def baseStart_8304371 : Nat := 118140960795 + 8304371 * 2 ^ 59
def prefixEnd_8304371 : Nat := 4983230072969 + 3 ^ 40 * 8304371 * 2
def baseEnd_8304371 : Nat := 1421377952086144614657133

theorem tailTrace_8304371 : CollatzResearch.WordTrace tailWord_8304371 prefixEnd_8304371 1421377952086144614657133 := by
  unfold tailWord_8304371
  simp only [CollatzResearch.WordTrace]
  refine ⟨302885293397689615497376967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201923528931793076998251311 302885293397689615497376967)
  ·
    refine ⟨454327940096534423246065451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302885293397689615497376967 454327940096534423246065451)
    ·
      refine ⟨681491910144801634869098177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454327940096534423246065451 681491910144801634869098177)
      ·
        refine ⟨511118932608601226151823633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681491910144801634869098177 511118932608601226151823633)
        ·
          refine ⟨383339199456450919613867725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511118932608601226151823633 383339199456450919613867725)
          ·
            refine ⟨143752199796169094855200397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383339199456450919613867725 143752199796169094855200397)
            ·
              refine ⟨53907074923563410570700149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143752199796169094855200397 53907074923563410570700149)
              ·
                refine ⟨5053788274084069741003139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53907074923563410570700149 5053788274084069741003139)
                ·
                  refine ⟨7580682411126104611504709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053788274084069741003139 7580682411126104611504709)
                  ·
                    refine ⟨1421377952086144614657133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580682411126104611504709 1421377952086144614657133)
                    ·
                      rfl

theorem cell23_8304371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 4].length) (baseStart_8304371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304371 prefixEnd_8304371 := by exact prefixLift 8304371
  have htrace : WordTrace (prefixWord ++ tailWord_8304371) baseStart_8304371 baseEnd_8304371 := by
    simpa [prefixWord, tailWord_8304371, baseEnd_8304371] using wordTrace_append hprefix tailTrace_8304371
  have hstable : (prefixWord ++ tailWord_8304371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304371).length < 2 ^ (prefixWord ++ tailWord_8304371).sum := by decide
  have hdescent : baseEnd_8304371 < baseStart_8304371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304374 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_8304374 : Nat := 118140960795 + 8304374 * 2 ^ 59
def prefixEnd_8304374 : Nat := 4983230072969 + 3 ^ 40 * 8304374 * 2
def baseEnd_8304374 : Nat := 4264135396700397332233885

theorem tailTrace_8304374 : CollatzResearch.WordTrace tailWord_8304374 prefixEnd_8304374 4264135396700397332233885 := by
  unfold tailWord_8304374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930337676042421688108511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201923601877785831339824117 18930337676042421688108511)
  ·
    refine ⟨28395506514063632532162767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18930337676042421688108511 28395506514063632532162767)
    ·
      refine ⟨42593259771095448798244151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28395506514063632532162767 42593259771095448798244151)
      ·
        refine ⟨63889889656643173197366227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42593259771095448798244151 63889889656643173197366227)
        ·
          refine ⟨95834834484964759796049341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63889889656643173197366227 95834834484964759796049341)
          ·
            refine ⟨35938062931861784923518503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95834834484964759796049341 35938062931861784923518503)
            ·
              refine ⟨53907094397792677385277755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35938062931861784923518503 53907094397792677385277755)
              ·
                refine ⟨80860641596689016077916633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53907094397792677385277755 80860641596689016077916633)
                ·
                  refine ⟨60645481197516762058437475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80860641596689016077916633 60645481197516762058437475)
                  ·
                    refine ⟨90968221796275143087656213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60645481197516762058437475 90968221796275143087656213)
                    ·
                      refine ⟨4264135396700397332233885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90968221796275143087656213 4264135396700397332233885)
                      ·
                        rfl

theorem cell23_8304374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_8304374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304374 prefixEnd_8304374 := by exact prefixLift 8304374
  have htrace : WordTrace (prefixWord ++ tailWord_8304374) baseStart_8304374 baseEnd_8304374 := by
    simpa [prefixWord, tailWord_8304374, baseEnd_8304374] using wordTrace_append hprefix tailTrace_8304374
  have hstable : (prefixWord ++ tailWord_8304374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304374).length < 2 ^ (prefixWord ++ tailWord_8304374).sum := by decide
  have hdescent : baseEnd_8304374 < baseStart_8304374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304387 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_8304387 : Nat := 118140960795 + 8304387 * 2 ^ 59
def prefixEnd_8304387 : Nat := 4983230072969 + 3 ^ 40 * 8304387 * 2
def baseEnd_8304387 : Nat := 4264142071948905781371325

theorem tailTrace_8304387 : CollatzResearch.WordTrace tailWord_8304387 prefixEnd_8304387 4264142071948905781371325 := by
  unfold tailWord_8304387
  simp only [CollatzResearch.WordTrace]
  refine ⟨302885876965631650229959415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201923917977087766819972943 302885876965631650229959415)
  ·
    refine ⟨454328815448447475344939123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302885876965631650229959415 454328815448447475344939123)
    ·
      refine ⟨681493223172671213017408685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454328815448447475344939123 681493223172671213017408685)
      ·
        refine ⟨255559958689751704881528257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681493223172671213017408685 255559958689751704881528257)
        ·
          refine ⟨191669969017313778661146193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255559958689751704881528257 191669969017313778661146193)
          ·
            refine ⟨143752476762985333995859645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191669969017313778661146193 143752476762985333995859645)
            ·
              refine ⟨53907178786119500248447367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143752476762985333995859645 53907178786119500248447367)
              ·
                refine ⟨80860768179179250372671051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53907178786119500248447367 80860768179179250372671051)
                ·
                  refine ⟨121291152268768875559006577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80860768179179250372671051 121291152268768875559006577)
                  ·
                    refine ⟨90968364201576656669254933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121291152268768875559006577 90968364201576656669254933)
                    ·
                      refine ⟨4264142071948905781371325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90968364201576656669254933 4264142071948905781371325)
                      ·
                        rfl

theorem cell23_8304387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_8304387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304387 prefixEnd_8304387 := by exact prefixLift 8304387
  have htrace : WordTrace (prefixWord ++ tailWord_8304387) baseStart_8304387 baseEnd_8304387 := by
    simpa [prefixWord, tailWord_8304387, baseEnd_8304387] using wordTrace_append hprefix tailTrace_8304387
  have hstable : (prefixWord ++ tailWord_8304387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304387).length < 2 ^ (prefixWord ++ tailWord_8304387).sum := by decide
  have hdescent : baseEnd_8304387 < baseStart_8304387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304388 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_8304388 : Nat := 118140960795 + 8304388 * 2 ^ 59
def prefixEnd_8304388 : Nat := 4983230072969 + 3 ^ 40 * 8304388 * 2
def baseEnd_8304388 : Nat := 1421380861809853425819607

theorem tailTrace_8304388 : CollatzResearch.WordTrace tailWord_8304388 prefixEnd_8304388 1421380861809853425819607 := by
  unfold tailWord_8304388
  simp only [CollatzResearch.WordTrace]
  refine ⟨151442956719314013700372909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201923942292418684933830545 151442956719314013700372909)
  ·
    refine ⟨56791108769742755137639841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151442956719314013700372909 56791108769742755137639841)
    ·
      refine ⟨42593331577307066353229881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56791108769742755137639841 42593331577307066353229881)
      ·
        refine ⟨31944998682980299764922411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42593331577307066353229881 31944998682980299764922411)
        ·
          refine ⟨47917498024470449647383617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31944998682980299764922411 47917498024470449647383617)
          ·
            refine ⟨35938123518352837235537713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47917498024470449647383617 35938123518352837235537713)
            ·
              refine ⟨26953592638764627926653285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35938123518352837235537713 26953592638764627926653285)
              ·
                refine ⟨5053798619768367736247491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26953592638764627926653285 5053798619768367736247491)
                ·
                  refine ⟨7580697929652551604371237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053798619768367736247491 7580697929652551604371237)
                  ·
                    refine ⟨1421380861809853425819607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580697929652551604371237 1421380861809853425819607)
                    ·
                      rfl

theorem cell23_8304388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_8304388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304388 prefixEnd_8304388 := by exact prefixLift 8304388
  have htrace : WordTrace (prefixWord ++ tailWord_8304388) baseStart_8304388 baseEnd_8304388 := by
    simpa [prefixWord, tailWord_8304388, baseEnd_8304388] using wordTrace_append hprefix tailTrace_8304388
  have hstable : (prefixWord ++ tailWord_8304388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304388).length < 2 ^ (prefixWord ++ tailWord_8304388).sum := by decide
  have hdescent : baseEnd_8304388 < baseStart_8304388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304421 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 5, 2]
def baseStart_8304421 : Nat := 118140960795 + 8304421 * 2 ^ 59
def prefixEnd_8304421 : Nat := 4983230072969 + 3 ^ 40 * 8304421 * 2
def baseEnd_8304421 : Nat := 4264159530291158648346169

theorem tailTrace_8304421 : CollatzResearch.WordTrace tailWord_8304421 prefixEnd_8304421 4264159530291158648346169 := by
  unfold tailWord_8304421
  simp only [CollatzResearch.WordTrace]
  refine ⟨302887117047508474036697117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201924744698338982691131411 302887117047508474036697117)
  ·
    refine ⟨113582668892815677763761419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302887117047508474036697117 113582668892815677763761419)
    ·
      refine ⟨170374003339223516645642129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113582668892815677763761419 170374003339223516645642129)
      ·
        refine ⟨127780502504417637484231597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170374003339223516645642129 127780502504417637484231597)
        ·
          refine ⟨47917688439156614056586849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127780502504417637484231597 47917688439156614056586849)
          ·
            refine ⟨35938266329367460542440137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47917688439156614056586849 35938266329367460542440137)
            ·
              refine ⟨26953699747025595406830103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35938266329367460542440137 26953699747025595406830103)
              ·
                refine ⟨40430549620538393110245155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26953699747025595406830103 40430549620538393110245155)
                ·
                  refine ⟨60645824430807589665367733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40430549620538393110245155 60645824430807589665367733)
                  ·
                    refine ⟨5685546040388211531128225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60645824430807589665367733 5685546040388211531128225)
                    ·
                      refine ⟨4264159530291158648346169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685546040388211531128225 4264159530291158648346169)
                      ·
                        rfl

theorem cell23_8304421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_8304421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304421 prefixEnd_8304421 := by exact prefixLift 8304421
  have htrace : WordTrace (prefixWord ++ tailWord_8304421) baseStart_8304421 baseEnd_8304421 := by
    simpa [prefixWord, tailWord_8304421, baseEnd_8304421] using wordTrace_append hprefix tailTrace_8304421
  have hstable : (prefixWord ++ tailWord_8304421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304421).length < 2 ^ (prefixWord ++ tailWord_8304421).sum := by decide
  have hdescent : baseEnd_8304421 < baseStart_8304421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304445 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_8304445 : Nat := 118140960795 + 8304445 * 2 ^ 59
def prefixEnd_8304445 : Nat := 4983230072969 + 3 ^ 40 * 8304445 * 2
def baseEnd_8304445 : Nat := 4264171853826866554446059

theorem tailTrace_8304445 : CollatzResearch.WordTrace tailWord_8304445 prefixEnd_8304445 4264171853826866554446059 := by
  unfold tailWord_8304445
  simp only [CollatzResearch.WordTrace]
  refine ⟨302887992399421526135570789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201925328266281017423713859 302887992399421526135570789)
  ·
    refine ⟨56791498574891536150419523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302887992399421526135570789 56791498574891536150419523)
    ·
      refine ⟨85187247862337304225629285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56791498574891536150419523 85187247862337304225629285)
      ·
        refine ⟨15972608974188244542305491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85187247862337304225629285 15972608974188244542305491)
        ·
          refine ⟨23958913461282366813458237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15972608974188244542305491 23958913461282366813458237)
          ·
            refine ⟨8984592547980887555046839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23958913461282366813458237 8984592547980887555046839)
            ·
              refine ⟨13476888821971331332570259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984592547980887555046839 13476888821971331332570259)
              ·
                refine ⟨20215333232956996998855389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13476888821971331332570259 20215333232956996998855389)
                ·
                  refine ⟨7580749962358873874570771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20215333232956996998855389 7580749962358873874570771)
                  ·
                    refine ⟨11371124943538310811856157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580749962358873874570771 11371124943538310811856157)
                    ·
                      refine ⟨4264171853826866554446059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371124943538310811856157 4264171853826866554446059)
                      ·
                        rfl

theorem cell23_8304445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_8304445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304445 prefixEnd_8304445 := by exact prefixLift 8304445
  have htrace : WordTrace (prefixWord ++ tailWord_8304445) baseStart_8304445 baseEnd_8304445 := by
    simpa [prefixWord, tailWord_8304445, baseEnd_8304445] using wordTrace_append hprefix tailTrace_8304445
  have hstable : (prefixWord ++ tailWord_8304445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304445).length < 2 ^ (prefixWord ++ tailWord_8304445).sum := by decide
  have hdescent : baseEnd_8304445 < baseStart_8304445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304464 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_8304464 : Nat := 118140960795 + 8304464 * 2 ^ 59
def prefixEnd_8304464 : Nat := 4983230072969 + 3 ^ 40 * 8304464 * 2
def baseEnd_8304464 : Nat := 4264181609959301980108471

theorem tailTrace_8304464 : CollatzResearch.WordTrace tailWord_8304464 prefixEnd_8304464 4264181609959301980108471 := by
  unfold tailWord_8304464
  simp only [CollatzResearch.WordTrace]
  refine ⟨151444342693176346190256223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201925790257568461587008297 151444342693176346190256223)
  ·
    refine ⟨227166514039764519285384335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151444342693176346190256223 227166514039764519285384335)
    ·
      refine ⟨340749771059646778928076503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227166514039764519285384335 340749771059646778928076503)
      ·
        refine ⟨511124656589470168392114755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340749771059646778928076503 511124656589470168392114755)
        ·
          refine ⟨766686984884205252588172133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511124656589470168392114755 766686984884205252588172133)
          ·
            refine ⟨143753809665788484860282275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 766686984884205252588172133 143753809665788484860282275)
            ·
              refine ⟨215630714498682727290423413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143753809665788484860282275 215630714498682727290423413)
              ·
                refine ⟨20215379484251505683477195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215630714498682727290423413 20215379484251505683477195)
                ·
                  refine ⟨30323069226377258525215793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20215379484251505683477195 30323069226377258525215793)
                  ·
                    refine ⟨22742301919782943893911845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30323069226377258525215793 22742301919782943893911845)
                    ·
                      refine ⟨4264181609959301980108471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22742301919782943893911845 4264181609959301980108471)
                      ·
                        rfl

theorem cell23_8304464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_8304464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304464 prefixEnd_8304464 := by exact prefixLift 8304464
  have htrace : WordTrace (prefixWord ++ tailWord_8304464) baseStart_8304464 baseEnd_8304464 := by
    simpa [prefixWord, tailWord_8304464, baseEnd_8304464] using wordTrace_append hprefix tailTrace_8304464
  have hstable : (prefixWord ++ tailWord_8304464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304464).length < 2 ^ (prefixWord ++ tailWord_8304464).sum := by decide
  have hdescent : baseEnd_8304464 < baseStart_8304464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304468 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_8304468 : Nat := 118140960795 + 8304468 * 2 ^ 59
def prefixEnd_8304468 : Nat := 4983230072969 + 3 ^ 40 * 8304468 * 2
def baseEnd_8304468 : Nat := 4264183663881919964458453

theorem tailTrace_8304468 : CollatzResearch.WordTrace tailWord_8304468 prefixEnd_8304468 4264183663881919964458453 := by
  unfold tailWord_8304468
  simp only [CollatzResearch.WordTrace]
  refine ⟨151444415639169100531829029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201925887518892134042438705 151444415639169100531829029)
  ·
    refine ⟨28395827932344206349717943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151444415639169100531829029 28395827932344206349717943)
    ·
      refine ⟨42593741898516309524576915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28395827932344206349717943 42593741898516309524576915)
      ·
        refine ⟨63890612847774464286865373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42593741898516309524576915 63890612847774464286865373)
        ·
          refine ⟨23958979817915424107574515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63890612847774464286865373 23958979817915424107574515)
          ·
            refine ⟨35938469726873136161361773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23958979817915424107574515 35938469726873136161361773)
            ·
              refine ⟨13476926147577426060510665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35938469726873136161361773 13476926147577426060510665)
              ·
                refine ⟨10107694610683069545382999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13476926147577426060510665 10107694610683069545382999)
                ·
                  refine ⟨15161541916024604318074499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10107694610683069545382999 15161541916024604318074499)
                  ·
                    refine ⟨22742312874036906477111749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15161541916024604318074499 22742312874036906477111749)
                    ·
                      refine ⟨4264183663881919964458453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22742312874036906477111749 4264183663881919964458453)
                      ·
                        rfl

theorem cell23_8304468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_8304468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304468 prefixEnd_8304468 := by exact prefixLift 8304468
  have htrace : WordTrace (prefixWord ++ tailWord_8304468) baseStart_8304468 baseEnd_8304468 := by
    simpa [prefixWord, tailWord_8304468, baseEnd_8304468] using wordTrace_append hprefix tailTrace_8304468
  have hstable : (prefixWord ++ tailWord_8304468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304468).length < 2 ^ (prefixWord ++ tailWord_8304468).sum := by decide
  have hdescent : baseEnd_8304468 < baseStart_8304468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304485 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 1, 2, 2]
def baseStart_8304485 : Nat := 118140960795 + 8304485 * 2 ^ 59
def prefixEnd_8304485 : Nat := 4983230072969 + 3 ^ 40 * 8304485 * 2
def baseEnd_8304485 : Nat := 4264192393053046397945875

theorem tailTrace_8304485 : CollatzResearch.WordTrace tailWord_8304485 prefixEnd_8304485 4264192393053046397945875 := by
  unfold tailWord_8304485
  simp only [CollatzResearch.WordTrace]
  refine ⟨302889451319276612967026909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201926300879517741978017939 302889451319276612967026909)
  ·
    refine ⟨113583544244728729862635091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302889451319276612967026909 113583544244728729862635091)
    ·
      refine ⟨170375316367093094793952637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113583544244728729862635091 170375316367093094793952637)
      ·
        refine ⟨63890743637659910547732239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170375316367093094793952637 63890743637659910547732239)
        ·
          refine ⟨95836115456489865821598359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63890743637659910547732239 95836115456489865821598359)
          ·
            refine ⟨143754173184734798732397539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95836115456489865821598359 143754173184734798732397539)
            ·
              refine ⟨215631259777102198098596309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143754173184734798732397539 215631259777102198098596309)
              ·
                refine ⟨5053857651025832767935851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215631259777102198098596309 5053857651025832767935851)
                ·
                  refine ⟨7580786476538749151903777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053857651025832767935851 7580786476538749151903777)
                  ·
                    refine ⟨5685589857404061863927833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7580786476538749151903777 5685589857404061863927833)
                    ·
                      refine ⟨4264192393053046397945875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685589857404061863927833 4264192393053046397945875)
                      ·
                        rfl

theorem cell23_8304485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_8304485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304485 prefixEnd_8304485 := by exact prefixLift 8304485
  have htrace : WordTrace (prefixWord ++ tailWord_8304485) baseStart_8304485 baseEnd_8304485 := by
    simpa [prefixWord, tailWord_8304485, baseEnd_8304485] using wordTrace_append hprefix tailTrace_8304485
  have hstable : (prefixWord ++ tailWord_8304485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304485).length < 2 ^ (prefixWord ++ tailWord_8304485).sum := by decide
  have hdescent : baseEnd_8304485 < baseStart_8304485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304501 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_8304501 : Nat := 118140960795 + 8304501 * 2 ^ 59
def prefixEnd_8304501 : Nat := 4983230072969 + 3 ^ 40 * 8304501 * 2
def baseEnd_8304501 : Nat := 4264200608743518335345801

theorem tailTrace_8304501 : CollatzResearch.WordTrace tailWord_8304501 prefixEnd_8304501 4264200608743518335345801 := by
  unfold tailWord_8304501
  simp only [CollatzResearch.WordTrace]
  refine ⟨302890034887218647699609357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201926689924812431799739571 302890034887218647699609357)
  ·
    refine ⟨113583763082706992887353509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302890034887218647699609357 113583763082706992887353509)
    ·
      refine ⟨21296955578007561166378783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113583763082706992887353509 21296955578007561166378783)
      ·
        refine ⟨31945433367011341749568175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21296955578007561166378783 31945433367011341749568175)
        ·
          refine ⟨47918150050517012624352263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31945433367011341749568175 47918150050517012624352263)
          ·
            refine ⟨71877225075775518936528395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47918150050517012624352263 71877225075775518936528395)
            ·
              refine ⟨107815837613663278404792593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71877225075775518936528395 107815837613663278404792593)
              ·
                refine ⟨80861878210247458803594445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107815837613663278404792593 80861878210247458803594445)
                ·
                  refine ⟨30323204328842797051347917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80861878210247458803594445 30323204328842797051347917)
                  ·
                    refine ⟨11371201623316048894255469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30323204328842797051347917 11371201623316048894255469)
                    ·
                      refine ⟨4264200608743518335345801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371201623316048894255469 4264200608743518335345801)
                      ·
                        rfl

theorem cell23_8304501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_8304501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304501 prefixEnd_8304501 := by exact prefixLift 8304501
  have htrace : WordTrace (prefixWord ++ tailWord_8304501) baseStart_8304501 baseEnd_8304501 := by
    simpa [prefixWord, tailWord_8304501, baseEnd_8304501] using wordTrace_append hprefix tailTrace_8304501
  have hstable : (prefixWord ++ tailWord_8304501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304501).length < 2 ^ (prefixWord ++ tailWord_8304501).sum := by decide
  have hdescent : baseEnd_8304501 < baseStart_8304501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304524 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_8304524 : Nat := 118140960795 + 8304524 * 2 ^ 59
def prefixEnd_8304524 : Nat := 4983230072969 + 3 ^ 40 * 8304524 * 2
def baseEnd_8304524 : Nat := 4264212418798571745358195

theorem tailTrace_8304524 : CollatzResearch.WordTrace tailWord_8304524 prefixEnd_8304524 4264212418798571745358195 := by
  unfold tailWord_8304524
  simp only [CollatzResearch.WordTrace]
  refine ⟨151445436883067661313848313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201927249177423548418464417 151445436883067661313848313)
  ·
    refine ⟨113584077662300745985386235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151445436883067661313848313 113584077662300745985386235)
    ·
      refine ⟨170376116493451118978079353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113584077662300745985386235 170376116493451118978079353)
      ·
        refine ⟨127782087370088339233559515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170376116493451118978079353 127782087370088339233559515)
        ·
          refine ⟨191673131055132508850339273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127782087370088339233559515 191673131055132508850339273)
          ·
            refine ⟨143754848291349381637754455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191673131055132508850339273 143754848291349381637754455)
            ·
              refine ⟨215632272437024072456631683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143754848291349381637754455 215632272437024072456631683)
              ·
                refine ⟨323448408655536108684947525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215632272437024072456631683 323448408655536108684947525)
                ·
                  refine ⟨60646576622913020378427661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323448408655536108684947525 60646576622913020378427661)
                  ·
                    refine ⟨22742466233592382641910373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60646576622913020378427661 22742466233592382641910373)
                    ·
                      refine ⟨4264212418798571745358195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22742466233592382641910373 4264212418798571745358195)
                      ·
                        rfl

theorem cell23_8304524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_8304524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304524 prefixEnd_8304524 := by exact prefixLift 8304524
  have htrace : WordTrace (prefixWord ++ tailWord_8304524) baseStart_8304524 baseEnd_8304524 := by
    simpa [prefixWord, tailWord_8304524, baseEnd_8304524] using wordTrace_append hprefix tailTrace_8304524
  have hstable : (prefixWord ++ tailWord_8304524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304524).length < 2 ^ (prefixWord ++ tailWord_8304524).sum := by decide
  have hdescent : baseEnd_8304524 < baseStart_8304524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304544 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5]
def baseStart_8304544 : Nat := 118140960795 + 8304544 * 2 ^ 59
def prefixEnd_8304544 : Nat := 4983230072969 + 3 ^ 40 * 8304544 * 2
def baseEnd_8304544 : Nat := 4264222688411661667108103

theorem tailTrace_8304544 : CollatzResearch.WordTrace tailWord_8304544 prefixEnd_8304544 4264222688411661667108103 := by
  unfold tailWord_8304544
  simp only [CollatzResearch.WordTrace]
  refine ⟨151445801613031433021712343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201927735484041910695616457 151445801613031433021712343)
  ·
    refine ⟨227168702419547149532568515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151445801613031433021712343 227168702419547149532568515)
    ·
      refine ⟨340753053629320724298852773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227168702419547149532568515 340753053629320724298852773)
      ·
        refine ⟨63891197555497635806034895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340753053629320724298852773 63891197555497635806034895)
        ·
          refine ⟨95836796333246453709052343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63891197555497635806034895 95836796333246453709052343)
          ·
            refine ⟨143755194499869680563578515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95836796333246453709052343 143755194499869680563578515)
            ·
              refine ⟨215632791749804520845367773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143755194499869680563578515 215632791749804520845367773)
              ·
                refine ⟨80862296906176695317012915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215632791749804520845367773 80862296906176695317012915)
                ·
                  refine ⟨121293445359265042975519373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80862296906176695317012915 121293445359265042975519373)
                  ·
                    refine ⟨45485042009724391115819765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121293445359265042975519373 45485042009724391115819765)
                    ·
                      refine ⟨4264222688411661667108103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45485042009724391115819765 4264222688411661667108103)
                      ·
                        rfl

theorem cell23_8304544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_8304544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304544 prefixEnd_8304544 := by exact prefixLift 8304544
  have htrace : WordTrace (prefixWord ++ tailWord_8304544) baseStart_8304544 baseEnd_8304544 := by
    simpa [prefixWord, tailWord_8304544, baseEnd_8304544] using wordTrace_append hprefix tailTrace_8304544
  have hstable : (prefixWord ++ tailWord_8304544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304544).length < 2 ^ (prefixWord ++ tailWord_8304544).sum := by decide
  have hdescent : baseEnd_8304544 < baseStart_8304544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304551 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 2, 6]
def baseStart_8304551 : Nat := 118140960795 + 8304551 * 2 ^ 59
def prefixEnd_8304551 : Nat := 4983230072969 + 3 ^ 40 * 8304551 * 2
def baseEnd_8304551 : Nat := 1421408760925414379906857

theorem tailTrace_8304551 : CollatzResearch.WordTrace tailWord_8304551 prefixEnd_8304551 1421408760925414379906857 := by
  unfold tailWord_8304551
  simp only [CollatzResearch.WordTrace]
  refine ⟨302891858537037506238929507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201927905691358337492619671 302891858537037506238929507)
  ·
    refine ⟨454337787805556259358394261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302891858537037506238929507 454337787805556259358394261)
    ·
      refine ⟨21297083803385449657424731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 454337787805556259358394261 21297083803385449657424731)
      ·
        refine ⟨31945625705078174486137097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21297083803385449657424731 31945625705078174486137097)
        ·
          refine ⟨23959219278808630864602823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31945625705078174486137097 23959219278808630864602823)
          ·
            refine ⟨35938828918212946296904235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23959219278808630864602823 35938828918212946296904235)
            ·
              refine ⟨53908243377319419445356353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35938828918212946296904235 53908243377319419445356353)
              ·
                refine ⟨40431182532989564584017265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53908243377319419445356353 40431182532989564584017265)
                ·
                  refine ⟨30323386899742173438012949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40431182532989564584017265 30323386899742173438012949)
                  ·
                    refine ⟨1421408760925414379906857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30323386899742173438012949 1421408760925414379906857)
                    ·
                      rfl

theorem cell23_8304551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_8304551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304551 prefixEnd_8304551 := by exact prefixLift 8304551
  have htrace : WordTrace (prefixWord ++ tailWord_8304551) baseStart_8304551 baseEnd_8304551 := by
    simpa [prefixWord, tailWord_8304551, baseEnd_8304551] using wordTrace_append hprefix tailTrace_8304551
  have hstable : (prefixWord ++ tailWord_8304551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304551).length < 2 ^ (prefixWord ++ tailWord_8304551).sum := by decide
  have hdescent : baseEnd_8304551 < baseStart_8304551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304552 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_8304552 : Nat := 118140960795 + 8304552 * 2 ^ 59
def prefixEnd_8304552 : Nat := 4983230072969 + 3 ^ 40 * 8304552 * 2
def baseEnd_8304552 : Nat := 4264226796256897635808067

theorem tailTrace_8304552 : CollatzResearch.WordTrace tailWord_8304552 prefixEnd_8304552 4264226796256897635808067 := by
  unfold tailWord_8304552
  simp only [CollatzResearch.WordTrace]
  refine ⟨151445947505016941704857955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201927930006689255606477273 151445947505016941704857955)
  ·
    refine ⟨227168921257525412557286933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151445947505016941704857955 227168921257525412557286933)
    ·
      refine ⟨10648543183946503713622825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227168921257525412557286933 10648543183946503713622825)
      ·
        refine ⟨7986407387959877785217119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10648543183946503713622825 7986407387959877785217119)
        ·
          refine ⟨11979611081939816677825679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986407387959877785217119 11979611081939816677825679)
          ·
            refine ⟨17969416622909725016738519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979611081939816677825679 17969416622909725016738519)
            ·
              refine ⟨26954124934364587525107779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17969416622909725016738519 26954124934364587525107779)
              ·
                refine ⟨40431187401546881287661669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26954124934364587525107779 40431187401546881287661669)
                ·
                  refine ⟨7580847637790040241436563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40431187401546881287661669 7580847637790040241436563)
                  ·
                    refine ⟨11371271456685060362154845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580847637790040241436563 11371271456685060362154845)
                    ·
                      refine ⟨4264226796256897635808067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371271456685060362154845 4264226796256897635808067)
                      ·
                        rfl

theorem cell23_8304552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_8304552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304552 prefixEnd_8304552 := by exact prefixLift 8304552
  have htrace : WordTrace (prefixWord ++ tailWord_8304552) baseStart_8304552 baseEnd_8304552 := by
    simpa [prefixWord, tailWord_8304552, baseEnd_8304552] using wordTrace_append hprefix tailTrace_8304552
  have hstable : (prefixWord ++ tailWord_8304552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304552).length < 2 ^ (prefixWord ++ tailWord_8304552).sum := by decide
  have hdescent : baseEnd_8304552 < baseStart_8304552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304611 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 4, 5]
def baseStart_8304611 : Nat := 118140960795 + 8304611 * 2 ^ 59
def prefixEnd_8304611 : Nat := 4983230072969 + 3 ^ 40 * 8304611 * 2
def baseEnd_8304611 : Nat := 1421419030538504301656765

theorem tailTrace_8304611 : CollatzResearch.WordTrace tailWord_8304611 prefixEnd_8304611 1421419030538504301656765 := by
  unfold tailWord_8304611
  simp only [CollatzResearch.WordTrace]
  refine ⟨302894046916820136486113687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201929364611213424324075791 302894046916820136486113687)
  ·
    refine ⟨454341070375230204729170531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302894046916820136486113687 454341070375230204729170531)
    ·
      refine ⟨681511605562845307093755797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454341070375230204729170531 681511605562845307093755797)
      ·
        refine ⟨31945856510758373770019803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 681511605562845307093755797 31945856510758373770019803)
        ·
          refine ⟨47918784766137560655029705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31945856510758373770019803 47918784766137560655029705)
          ·
            refine ⟨35939088574603170491272279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47918784766137560655029705 35939088574603170491272279)
            ·
              refine ⟨53908632861904755736908419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35939088574603170491272279 53908632861904755736908419)
              ·
                refine ⟨80862949292857133605362629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53908632861904755736908419 80862949292857133605362629)
                ·
                  refine ⟨15161802992410712551005493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80862949292857133605362629 15161802992410712551005493)
                  ·
                    refine ⟨1421419030538504301656765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15161802992410712551005493 1421419030538504301656765)
                    ·
                      rfl

theorem cell23_8304611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 5].length) (baseStart_8304611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304611 prefixEnd_8304611 := by exact prefixLift 8304611
  have htrace : WordTrace (prefixWord ++ tailWord_8304611) baseStart_8304611 baseEnd_8304611 := by
    simpa [prefixWord, tailWord_8304611, baseEnd_8304611] using wordTrace_append hprefix tailTrace_8304611
  have hstable : (prefixWord ++ tailWord_8304611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304611).length < 2 ^ (prefixWord ++ tailWord_8304611).sum := by decide
  have hdescent : baseEnd_8304611 < baseStart_8304611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304615 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 7]
def baseStart_8304615 : Nat := 118140960795 + 8304615 * 2 ^ 59
def prefixEnd_8304615 : Nat := 4983230072969 + 3 ^ 40 * 8304615 * 2
def baseEnd_8304615 : Nat := 473806571726458987702253

theorem tailTrace_8304615 : CollatzResearch.WordTrace tailWord_8304615 prefixEnd_8304615 473806571726458987702253 := by
  unfold tailWord_8304615
  simp only [CollatzResearch.WordTrace]
  refine ⟨302894192808805645169259299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201929461872537096779506199 302894192808805645169259299)
  ·
    refine ⟨454341289213208467753888949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302894192808805645169259299 454341289213208467753888949)
    ·
      refine ⟨42594495863738293851927089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 454341289213208467753888949 42594495863738293851927089)
      ·
        refine ⟨31945871897803720388945317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42594495863738293851927089 31945871897803720388945317)
        ·
          refine ⟨5989850980838197572927247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31945871897803720388945317 5989850980838197572927247)
          ·
            refine ⟨8984776471257296359390871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989850980838197572927247 8984776471257296359390871)
            ·
              refine ⟨13477164706885944539086307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984776471257296359390871 13477164706885944539086307)
              ·
                refine ⟨20215747060328916808629461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477164706885944539086307 20215747060328916808629461)
                ·
                  refine ⟨473806571726458987702253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20215747060328916808629461 473806571726458987702253)
                  ·
                    rfl

theorem cell23_8304615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 7].length) (baseStart_8304615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304615 prefixEnd_8304615 := by exact prefixLift 8304615
  have htrace : WordTrace (prefixWord ++ tailWord_8304615) baseStart_8304615 baseEnd_8304615 := by
    simpa [prefixWord, tailWord_8304615, baseEnd_8304615] using wordTrace_append hprefix tailTrace_8304615
  have hstable : (prefixWord ++ tailWord_8304615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304615).length < 2 ^ (prefixWord ++ tailWord_8304615).sum := by decide
  have hdescent : baseEnd_8304615 < baseStart_8304615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304618 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_8304618 : Nat := 118140960795 + 8304618 * 2 ^ 59
def prefixEnd_8304618 : Nat := 4983230072969 + 3 ^ 40 * 8304618 * 2
def baseEnd_8304618 : Nat := 4264260685980094377582763

theorem tailTrace_8304618 : CollatzResearch.WordTrace tailWord_8304618 prefixEnd_8304618 4264260685980094377582763 := by
  unfold tailWord_8304618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75723575556948694170404627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201929534818529851121079005 75723575556948694170404627)
  ·
    refine ⟨113585363335423041255606941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75723575556948694170404627 113585363335423041255606941)
    ·
      refine ⟨42594511250783640470852603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113585363335423041255606941 42594511250783640470852603)
      ·
        refine ⟨63891766876175460706278905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42594511250783640470852603 63891766876175460706278905)
        ·
          refine ⟨47918825157131595529709179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63891766876175460706278905 47918825157131595529709179)
          ·
            refine ⟨71878237735697393294563769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47918825157131595529709179 71878237735697393294563769)
            ·
              refine ⟨53908678301773044970922827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71878237735697393294563769 53908678301773044970922827)
              ·
                refine ⟨80863017452659567456384241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53908678301773044970922827 80863017452659567456384241)
                ·
                  refine ⟨60647263089494675592288181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80863017452659567456384241 60647263089494675592288181)
                  ·
                    refine ⟨5685680914640125836777017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60647263089494675592288181 5685680914640125836777017)
                    ·
                      refine ⟨4264260685980094377582763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5685680914640125836777017 4264260685980094377582763)
                      ·
                        rfl

theorem cell23_8304618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_8304618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304618 prefixEnd_8304618 := by exact prefixLift 8304618
  have htrace : WordTrace (prefixWord ++ tailWord_8304618) baseStart_8304618 baseEnd_8304618 := by
    simpa [prefixWord, tailWord_8304618, baseEnd_8304618] using wordTrace_append hprefix tailTrace_8304618
  have hstable : (prefixWord ++ tailWord_8304618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304618).length < 2 ^ (prefixWord ++ tailWord_8304618).sum := by decide
  have hdescent : baseEnd_8304618 < baseStart_8304618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304648 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_8304648 : Nat := 118140960795 + 8304648 * 2 ^ 59
def prefixEnd_8304648 : Nat := 4983230072969 + 3 ^ 40 * 8304648 * 2
def baseEnd_8304648 : Nat := 4264276090399729260207625

theorem tailTrace_8304648 : CollatzResearch.WordTrace tailWord_8304648 prefixEnd_8304648 4264276090399729260207625 := by
  unfold tailWord_8304648
  simp only [CollatzResearch.WordTrace]
  refine ⟨151447698208843045902605299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201930264278457394536807065 151447698208843045902605299)
  ·
    refine ⟨227171547313264568853907949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151447698208843045902605299 227171547313264568853907949)
    ·
      refine ⟨85189330242474213320215481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227171547313264568853907949 85189330242474213320215481)
      ·
        refine ⟨63891997681855659990161611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85189330242474213320215481 63891997681855659990161611)
        ·
          refine ⟨95837996522783489985242417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63891997681855659990161611 95837996522783489985242417)
          ·
            refine ⟨71878497392087617488931813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95837996522783489985242417 71878497392087617488931813)
            ·
              refine ⟨13477218261016428279174715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71878497392087617488931813 13477218261016428279174715)
              ·
                refine ⟨20215827391524642418762073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477218261016428279174715 20215827391524642418762073)
                ·
                  refine ⟨15161870543643481814071555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20215827391524642418762073 15161870543643481814071555)
                  ·
                    refine ⟨22742805815465222721107333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15161870543643481814071555 22742805815465222721107333)
                    ·
                      refine ⟨4264276090399729260207625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22742805815465222721107333 4264276090399729260207625)
                      ·
                        rfl

theorem cell23_8304648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_8304648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304648 prefixEnd_8304648 := by exact prefixLift 8304648
  have htrace : WordTrace (prefixWord ++ tailWord_8304648) baseStart_8304648 baseEnd_8304648 := by
    simpa [prefixWord, tailWord_8304648, baseEnd_8304648] using wordTrace_append hprefix tailTrace_8304648
  have hstable : (prefixWord ++ tailWord_8304648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304648).length < 2 ^ (prefixWord ++ tailWord_8304648).sum := by decide
  have hdescent : baseEnd_8304648 < baseStart_8304648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304675 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 1, 4]
def baseStart_8304675 : Nat := 118140960795 + 8304675 * 2 ^ 59
def prefixEnd_8304675 : Nat := 4983230072969 + 3 ^ 40 * 8304675 * 2
def baseEnd_8304675 : Nat := 1421429984792466884856667

theorem tailTrace_8304675 : CollatzResearch.WordTrace tailWord_8304675 prefixEnd_8304675 1421429984792466884856667 := by
  unfold tailWord_8304675
  simp only [CollatzResearch.WordTrace]
  refine ⟨302896381188588275416443479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201930920792392183610962319 302896381188588275416443479)
  ·
    refine ⟨454344571782882413124665219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302896381188588275416443479 454344571782882413124665219)
    ·
      refine ⟨681516857674323619686997829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454344571782882413124665219 681516857674323619686997829)
      ·
        refine ⟨127784410813935678691312093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 681516857674323619686997829 127784410813935678691312093)
        ·
          refine ⟨47919154055225879509242035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127784410813935678691312093 47919154055225879509242035)
          ·
            refine ⟨71878731082838819263863053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47919154055225879509242035 71878731082838819263863053)
            ·
              refine ⟨26954524156064557223948645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71878731082838819263863053 26954524156064557223948645)
              ·
                refine ⟨5053973279262104479490371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26954524156064557223948645 5053973279262104479490371)
                ·
                  refine ⟨7580959918893156719235557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053973279262104479490371 7580959918893156719235557)
                  ·
                    refine ⟨1421429984792466884856667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580959918893156719235557 1421429984792466884856667)
                    ·
                      rfl

theorem cell23_8304675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 4].length) (baseStart_8304675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304675 prefixEnd_8304675 := by exact prefixLift 8304675
  have htrace : WordTrace (prefixWord ++ tailWord_8304675) baseStart_8304675 baseEnd_8304675 := by
    simpa [prefixWord, tailWord_8304675, baseEnd_8304675] using wordTrace_append hprefix tailTrace_8304675
  have hstable : (prefixWord ++ tailWord_8304675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304675).length < 2 ^ (prefixWord ++ tailWord_8304675).sum := by decide
  have hdescent : baseEnd_8304675 < baseStart_8304675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304692 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_8304692 : Nat := 118140960795 + 8304692 * 2 ^ 59
def prefixEnd_8304692 : Nat := 4983230072969 + 3 ^ 40 * 8304692 * 2
def baseEnd_8304692 : Nat := 1421432894516175696019141

theorem tailTrace_8304692 : CollatzResearch.WordTrace tailWord_8304692 prefixEnd_8304692 1421432894516175696019141 := by
  unfold tailWord_8304692
  simp only [CollatzResearch.WordTrace]
  refine ⟨151448500614763343659906165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201931334153017791546541553 151448500614763343659906165)
  ·
    refine ⟨14198296932634063468116203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151448500614763343659906165 14198296932634063468116203)
    ·
      refine ⟨21297445398951095202174305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14198296932634063468116203 21297445398951095202174305)
      ·
        refine ⟨15973084049213321401630729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21297445398951095202174305 15973084049213321401630729)
        ·
          refine ⟨11979813036909991051223047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15973084049213321401630729 11979813036909991051223047)
          ·
            refine ⟨17969719555364986576834571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979813036909991051223047 17969719555364986576834571)
            ·
              refine ⟨26954579333047479865251857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17969719555364986576834571 26954579333047479865251857)
              ·
                refine ⟨20215934499785609898938893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26954579333047479865251857 20215934499785609898938893)
                ·
                  refine ⟨7580975437419603712102085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20215934499785609898938893 7580975437419603712102085)
                  ·
                    refine ⟨1421432894516175696019141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580975437419603712102085 1421432894516175696019141)
                    ·
                      rfl

theorem cell23_8304692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_8304692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304692 prefixEnd_8304692 := by exact prefixLift 8304692
  have htrace : WordTrace (prefixWord ++ tailWord_8304692) baseStart_8304692 baseEnd_8304692 := by
    simpa [prefixWord, tailWord_8304692, baseEnd_8304692] using wordTrace_append hprefix tailTrace_8304692
  have hstable : (prefixWord ++ tailWord_8304692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304692).length < 2 ^ (prefixWord ++ tailWord_8304692).sum := by decide
  have hdescent : baseEnd_8304692 < baseStart_8304692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304722 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_8304722 : Nat := 118140960795 + 8304722 * 2 ^ 59
def prefixEnd_8304722 : Nat := 4983230072969 + 3 ^ 40 * 8304722 * 2
def baseEnd_8304722 : Nat := 473812676440906885631365

theorem tailTrace_8304722 : CollatzResearch.WordTrace tailWord_8304722 prefixEnd_8304722 473812676440906885631365 := by
  unfold tailWord_8304722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75724523854854500610851105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201932063612945334962269613 75724523854854500610851105)
  ·
    refine ⟨56793392891140875458138329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75724523854854500610851105 56793392891140875458138329)
    ·
      refine ⟨42595044668355656593603747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56793392891140875458138329 42595044668355656593603747)
      ·
        refine ⟨63892567002533484890405621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42595044668355656593603747 63892567002533484890405621)
        ·
          refine ⟨5989928156487514208475527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63892567002533484890405621 5989928156487514208475527)
          ·
            refine ⟨8984892234731271312713291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989928156487514208475527 8984892234731271312713291)
            ·
              refine ⟨13477338352096906969069937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984892234731271312713291 13477338352096906969069937)
              ·
                refine ⟨10108003764072680226802453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13477338352096906969069937 10108003764072680226802453)
                ·
                  refine ⟨473812676440906885631365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10108003764072680226802453 473812676440906885631365)
                  ·
                    rfl

theorem cell23_8304722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_8304722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304722 prefixEnd_8304722 := by exact prefixLift 8304722
  have htrace : WordTrace (prefixWord ++ tailWord_8304722) baseStart_8304722 baseEnd_8304722 := by
    simpa [prefixWord, tailWord_8304722, baseEnd_8304722] using wordTrace_append hprefix tailTrace_8304722
  have hstable : (prefixWord ++ tailWord_8304722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304722).length < 2 ^ (prefixWord ++ tailWord_8304722).sum := by decide
  have hdescent : baseEnd_8304722 < baseStart_8304722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304732 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_8304732 : Nat := 118140960795 + 8304732 * 2 ^ 59
def prefixEnd_8304732 : Nat := 4983230072969 + 3 ^ 40 * 8304732 * 2
def baseEnd_8304732 : Nat := 4264319222774706931557239

theorem tailTrace_8304732 : CollatzResearch.WordTrace tailWord_8304732 prefixEnd_8304732 4264319222774706931557239 := by
  unfold tailWord_8304732
  simp only [CollatzResearch.WordTrace]
  refine ⟨151449230074690887075634225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201932306766254516100845633 151449230074690887075634225)
  ·
    refine ⟨113586922556018165306725669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151449230074690887075634225 113586922556018165306725669)
    ·
      refine ⟨21297547979253405995011063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113586922556018165306725669 21297547979253405995011063)
      ·
        refine ⟨31946321968880108992516595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21297547979253405995011063 31946321968880108992516595)
        ·
          refine ⟨47919482953320163488774893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31946321968880108992516595 47919482953320163488774893)
          ·
            refine ⟨17969806107495061308290585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47919482953320163488774893 17969806107495061308290585)
            ·
              refine ⟨13477354580621295981217939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17969806107495061308290585 13477354580621295981217939)
              ·
                refine ⟨20216031870931943971826909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477354580621295981217939 20216031870931943971826909)
                ·
                  refine ⟨7581011951599478989435091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20216031870931943971826909 7581011951599478989435091)
                  ·
                    refine ⟨11371517927399218484152637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7581011951599478989435091 11371517927399218484152637)
                    ·
                      refine ⟨4264319222774706931557239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371517927399218484152637 4264319222774706931557239)
                      ·
                        rfl

theorem cell23_8304732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_8304732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304732 prefixEnd_8304732 := by exact prefixLift 8304732
  have htrace : WordTrace (prefixWord ++ tailWord_8304732) baseStart_8304732 baseEnd_8304732 := by
    simpa [prefixWord, tailWord_8304732, baseEnd_8304732] using wordTrace_append hprefix tailTrace_8304732
  have hstable : (prefixWord ++ tailWord_8304732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304732).length < 2 ^ (prefixWord ++ tailWord_8304732).sum := by decide
  have hdescent : baseEnd_8304732 < baseStart_8304732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304748 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_8304748 : Nat := 118140960795 + 8304748 * 2 ^ 59
def prefixEnd_8304748 : Nat := 4983230072969 + 3 ^ 40 * 8304748 * 2
def baseEnd_8304748 : Nat := 1421442479488392956319055

theorem tailTrace_8304748 : CollatzResearch.WordTrace tailWord_8304748 prefixEnd_8304748 1421442479488392956319055 := by
  unfold tailWord_8304748
  simp only [CollatzResearch.WordTrace]
  refine ⟨151449521858661904441925449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201932695811549205922567265 151449521858661904441925449)
  ·
    refine ⟨113587141393996428331444087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151449521858661904441925449 113587141393996428331444087)
    ·
      refine ⟨170380712090994642497166131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113587141393996428331444087 170380712090994642497166131)
      ·
        refine ⟨255571068136491963745749197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170380712090994642497166131 255571068136491963745749197)
        ·
          refine ⟨95839150551184486404655949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255571068136491963745749197 95839150551184486404655949)
          ·
            refine ⟨35939681456694182401745981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95839150551184486404655949 35939681456694182401745981)
            ·
              refine ⟨13477380546260318400654743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35939681456694182401745981 13477380546260318400654743)
              ·
                refine ⟨20216070819390477600982115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477380546260318400654743 20216070819390477600982115)
                ·
                  refine ⟨30324106229085716401473173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20216070819390477600982115 30324106229085716401473173)
                  ·
                    refine ⟨1421442479488392956319055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30324106229085716401473173 1421442479488392956319055)
                    ·
                      rfl

theorem cell23_8304748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_8304748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304748 prefixEnd_8304748 := by exact prefixLift 8304748
  have htrace : WordTrace (prefixWord ++ tailWord_8304748) baseStart_8304748 baseEnd_8304748 := by
    simpa [prefixWord, tailWord_8304748, baseEnd_8304748] using wordTrace_append hprefix tailTrace_8304748
  have hstable : (prefixWord ++ tailWord_8304748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304748).length < 2 ^ (prefixWord ++ tailWord_8304748).sum := by decide
  have hdescent : baseEnd_8304748 < baseStart_8304748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304775 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_8304775 : Nat := 118140960795 + 8304775 * 2 ^ 59
def prefixEnd_8304775 : Nat := 4983230072969 + 3 ^ 40 * 8304775 * 2
def baseEnd_8304775 : Nat := 4264341302442850263319541

theorem tailTrace_8304775 : CollatzResearch.WordTrace tailWord_8304775 prefixEnd_8304775 4264341302442850263319541 := by
  unfold tailWord_8304775
  simp only [CollatzResearch.WordTrace]
  refine ⟨302900028488225992495083779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201933352325483994996722519 302900028488225992495083779)
  ·
    refine ⟨454350042732338988742625669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302900028488225992495083779 454350042732338988742625669)
    ·
      refine ⟨85190633012313560389242313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454350042732338988742625669 85190633012313560389242313)
      ·
        refine ⟨63892974759235170291931735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85190633012313560389242313 63892974759235170291931735)
        ·
          refine ⟨95839462138852755437897603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63892974759235170291931735 95839462138852755437897603)
          ·
            refine ⟨143759193208279133156846405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95839462138852755437897603 143759193208279133156846405)
            ·
              refine ⟨26954848726552337466908701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143759193208279133156846405 26954848726552337466908701)
              ·
                refine ⟨10108068272457126550090763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26954848726552337466908701 10108068272457126550090763)
                ·
                  refine ⟨15162102408685689825136145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10108068272457126550090763 15162102408685689825136145)
                  ·
                    refine ⟨11371576806514267368852109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15162102408685689825136145 11371576806514267368852109)
                    ·
                      refine ⟨4264341302442850263319541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11371576806514267368852109 4264341302442850263319541)
                      ·
                        rfl

theorem cell23_8304775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_8304775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304775 prefixEnd_8304775 := by exact prefixLift 8304775
  have htrace : WordTrace (prefixWord ++ tailWord_8304775) baseStart_8304775 baseEnd_8304775 := by
    simpa [prefixWord, tailWord_8304775, baseEnd_8304775] using wordTrace_append hprefix tailTrace_8304775
  have hstable : (prefixWord ++ tailWord_8304775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304775).length < 2 ^ (prefixWord ++ tailWord_8304775).sum := by decide
  have hdescent : baseEnd_8304775 < baseStart_8304775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304778 : List Nat := [3, 1, 2, 3, 1, 4, 9]
def baseStart_8304778 : Nat := 118140960795 + 8304778 * 2 ^ 59
def prefixEnd_8304778 : Nat := 4983230072969 + 3 ^ 40 * 8304778 * 2
def baseEnd_8304778 : Nat := 52646207936849552488667

theorem tailTrace_8304778 : CollatzResearch.WordTrace tailWord_8304778 prefixEnd_8304778 52646207936849552488667 := by
  unfold tailWord_8304778
  simp only [CollatzResearch.WordTrace]
  refine ⟨75725034476803781001860747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201933425271476749338295325 75725034476803781001860747)
  ·
    refine ⟨113587551715205671502791121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75725034476803781001860747 113587551715205671502791121)
    ·
      refine ⟨85190663786404253627093341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113587551715205671502791121 85190663786404253627093341)
      ·
        refine ⟨31946498919901595110160003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85190663786404253627093341 31946498919901595110160003)
        ·
          refine ⟨47919748379852392665240005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31946498919901595110160003 47919748379852392665240005)
          ·
            refine ⟨8984952821222323624732501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47919748379852392665240005 8984952821222323624732501)
            ·
              refine ⟨52646207936849552488667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8984952821222323624732501 52646207936849552488667)
              ·
                rfl

theorem cell23_8304778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 9].length) (baseStart_8304778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304778 prefixEnd_8304778 := by exact prefixLift 8304778
  have htrace : WordTrace (prefixWord ++ tailWord_8304778) baseStart_8304778 baseEnd_8304778 := by
    simpa [prefixWord, tailWord_8304778, baseEnd_8304778] using wordTrace_append hprefix tailTrace_8304778
  have hstable : (prefixWord ++ tailWord_8304778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304778).length < 2 ^ (prefixWord ++ tailWord_8304778).sum := by decide
  have hdescent : baseEnd_8304778 < baseStart_8304778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304790 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_8304790 : Nat := 118140960795 + 8304790 * 2 ^ 59
def prefixEnd_8304790 : Nat := 4983230072969 + 3 ^ 40 * 8304790 * 2
def baseEnd_8304790 : Nat := 473816556072518633847997

theorem tailTrace_8304790 : CollatzResearch.WordTrace tailWord_8304790 prefixEnd_8304790 473816556072518633847997 := by
  unfold tailWord_8304790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931285973948228128554989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201933717055447766704586549 18931285973948228128554989)
  ·
    refine ⟨7099232240230585548208121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18931285973948228128554989 7099232240230585548208121)
    ·
      refine ⟨5324424180172939161156091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7099232240230585548208121 5324424180172939161156091)
      ·
        refine ⟨7986636270259408741734137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324424180172939161156091 7986636270259408741734137)
        ·
          refine ⟨5989977202694556556300603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7986636270259408741734137 5989977202694556556300603)
          ·
            refine ⟨8984965804041834834450905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989977202694556556300603 8984965804041834834450905)
            ·
              refine ⟨6738724353031376125838179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8984965804041834834450905 6738724353031376125838179)
              ·
                refine ⟨10108086529547064188757269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738724353031376125838179 10108086529547064188757269)
                ·
                  refine ⟨473816556072518633847997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10108086529547064188757269 473816556072518633847997)
                  ·
                    rfl

theorem cell23_8304790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_8304790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304790 prefixEnd_8304790 := by exact prefixLift 8304790
  have htrace : WordTrace (prefixWord ++ tailWord_8304790) baseStart_8304790 baseEnd_8304790 := by
    simpa [prefixWord, tailWord_8304790, baseEnd_8304790] using wordTrace_append hprefix tailTrace_8304790
  have hstable : (prefixWord ++ tailWord_8304790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304790).length < 2 ^ (prefixWord ++ tailWord_8304790).sum := by decide
  have hdescent : baseEnd_8304790 < baseStart_8304790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304799 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 2, 4]
def baseStart_8304799 : Nat := 118140960795 + 8304799 * 2 ^ 59
def prefixEnd_8304799 : Nat := 4983230072969 + 3 ^ 40 * 8304799 * 2
def baseEnd_8304799 : Nat := 1421451208659519389806477

theorem tailTrace_8304799 : CollatzResearch.WordTrace tailWord_8304799 prefixEnd_8304799 1421451208659519389806477 := by
  unfold tailWord_8304799
  simp only [CollatzResearch.WordTrace]
  refine ⟨302900903840139044593957451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201933935893426029729304967 302900903840139044593957451)
  ·
    refine ⟨454351355760208566890936177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302900903840139044593957451 454351355760208566890936177)
    ·
      refine ⟨340763516820156425168202133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454351355760208566890936177 340763516820156425168202133)
      ·
        refine ⟨15973289850944832429759475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340763516820156425168202133 15973289850944832429759475)
        ·
          refine ⟨23959934776417248644639213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15973289850944832429759475 23959934776417248644639213)
          ·
            refine ⟨8984975541156468241739705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23959934776417248644639213 8984975541156468241739705)
            ·
              refine ⟨6738731655867351181304779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8984975541156468241739705 6738731655867351181304779)
              ·
                refine ⟨10108097483801026771957169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738731655867351181304779 10108097483801026771957169)
                ·
                  refine ⟨7581073112850770078967877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10108097483801026771957169 7581073112850770078967877)
                  ·
                    refine ⟨1421451208659519389806477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7581073112850770078967877 1421451208659519389806477)
                    ·
                      rfl

theorem cell23_8304799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_8304799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304799 prefixEnd_8304799 := by exact prefixLift 8304799
  have htrace : WordTrace (prefixWord ++ tailWord_8304799) baseStart_8304799 baseEnd_8304799 := by
    simpa [prefixWord, tailWord_8304799, baseEnd_8304799] using wordTrace_append hprefix tailTrace_8304799
  have hstable : (prefixWord ++ tailWord_8304799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304799).length < 2 ^ (prefixWord ++ tailWord_8304799).sum := by decide
  have hdescent : baseEnd_8304799 < baseStart_8304799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304858 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_8304858 : Nat := 118140960795 + 8304858 * 2 ^ 59
def prefixEnd_8304858 : Nat := 4983230072969 + 3 ^ 40 * 8304858 * 2
def baseEnd_8304858 : Nat := 4264383921337173438581659

theorem tailTrace_8304858 : CollatzResearch.WordTrace tailWord_8304858 prefixEnd_8304858 4264383921337173438581659 := by
  unfold tailWord_8304858
  simp only [CollatzResearch.WordTrace]
  refine ⟨75725763936731324417588807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201935370497950198446903485 75725763936731324417588807)
  ·
    refine ⟨113588645905096986626383211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75725763936731324417588807 113588645905096986626383211)
    ·
      refine ⟨170382968857645479939574817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113588645905096986626383211 170382968857645479939574817)
      ·
        refine ⟨127787226643234109954681113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170382968857645479939574817 127787226643234109954681113)
        ·
          refine ⟨95840419982425582466010835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127787226643234109954681113 95840419982425582466010835)
          ·
            refine ⟨143760629973638373699016253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95840419982425582466010835 143760629973638373699016253)
            ·
              refine ⟨53910236240114390137131095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143760629973638373699016253 53910236240114390137131095)
              ·
                refine ⟨80865354360171585205696643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53910236240114390137131095 80865354360171585205696643)
                ·
                  refine ⟨121298031540257377808544965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80865354360171585205696643 121298031540257377808544965)
                  ·
                    refine ⟨22743380913798258339102181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121298031540257377808544965 22743380913798258339102181)
                    ·
                      refine ⟨4264383921337173438581659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22743380913798258339102181 4264383921337173438581659)
                      ·
                        rfl

theorem cell23_8304858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_8304858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304858 prefixEnd_8304858 := by exact prefixLift 8304858
  have htrace : WordTrace (prefixWord ++ tailWord_8304858) baseStart_8304858 baseEnd_8304858 := by
    simpa [prefixWord, tailWord_8304858, baseEnd_8304858] using wordTrace_append hprefix tailTrace_8304858
  have hstable : (prefixWord ++ tailWord_8304858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304858).length < 2 ^ (prefixWord ++ tailWord_8304858).sum := by decide
  have hdescent : baseEnd_8304858 < baseStart_8304858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304878 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_8304878 : Nat := 118140960795 + 8304878 * 2 ^ 59
def prefixEnd_8304878 : Nat := 4983230072969 + 3 ^ 40 * 8304878 * 2
def baseEnd_8304878 : Nat := 4264394190950263360331567

theorem tailTrace_8304878 : CollatzResearch.WordTrace tailWord_8304878 prefixEnd_8304878 4264394190950263360331567 := by
  unfold tailWord_8304878
  simp only [CollatzResearch.WordTrace]
  refine ⟨37862973150856605135760411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201935856804568560724055525 37862973150856605135760411)
  ·
    refine ⟨56794459726284907703640617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37862973150856605135760411 56794459726284907703640617)
    ·
      refine ⟨42595844794713680777730463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56794459726284907703640617 42595844794713680777730463)
      ·
        refine ⟨63893767192070521166595695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42595844794713680777730463 63893767192070521166595695)
        ·
          refine ⟨95840650788105781749893543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63893767192070521166595695 95840650788105781749893543)
          ·
            refine ⟨143760976182158672624840315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95840650788105781749893543 143760976182158672624840315)
            ·
              refine ⟨215641464273238008937260473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143760976182158672624840315 215641464273238008937260473)
              ·
                refine ⟨161731098204928506702945355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215641464273238008937260473 161731098204928506702945355)
                ·
                  refine ⟨242596647307392760054418033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161731098204928506702945355 242596647307392760054418033)
                  ·
                    refine ⟨181947485480544570040813525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242596647307392760054418033 181947485480544570040813525)
                    ·
                      refine ⟨4264394190950263360331567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181947485480544570040813525 4264394190950263360331567)
                      ·
                        rfl

theorem cell23_8304878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_8304878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304878 prefixEnd_8304878 := by exact prefixLift 8304878
  have htrace : WordTrace (prefixWord ++ tailWord_8304878) baseStart_8304878 baseEnd_8304878 := by
    simpa [prefixWord, tailWord_8304878, baseEnd_8304878] using wordTrace_append hprefix tailTrace_8304878
  have hstable : (prefixWord ++ tailWord_8304878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304878).length < 2 ^ (prefixWord ++ tailWord_8304878).sum := by decide
  have hdescent : baseEnd_8304878 < baseStart_8304878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8304908 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_8304908 : Nat := 118140960795 + 8304908 * 2 ^ 59
def prefixEnd_8304908 : Nat := 4983230072969 + 3 ^ 40 * 8304908 * 2
def baseEnd_8304908 : Nat := 4264409595369898242956429

theorem tailTrace_8304908 : CollatzResearch.WordTrace tailWord_8304908 prefixEnd_8304908 4264409595369898242956429 := by
  unfold tailWord_8304908
  simp only [CollatzResearch.WordTrace]
  refine ⟨151452439698372078104837689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201936586264496104139783585 151452439698372078104837689)
  ·
    refine ⟨113589329773779058578628267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151452439698372078104837689 113589329773779058578628267)
    ·
      refine ⟨170383994660668587867942401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113589329773779058578628267 170383994660668587867942401)
      ·
        refine ⟨127787995995501440900956801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170383994660668587867942401 127787995995501440900956801)
        ·
          refine ⟨95840996996626080675717601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127787995995501440900956801 95840996996626080675717601)
          ·
            refine ⟨71880747747469560506788201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95840996996626080675717601 71880747747469560506788201)
            ·
              refine ⟨53910560810602170380091151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71880747747469560506788201 53910560810602170380091151)
              ·
                refine ⟨80865841215903255570136727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53910560810602170380091151 80865841215903255570136727)
                ·
                  refine ⟨121298761823854883355205091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80865841215903255570136727 121298761823854883355205091)
                  ·
                    refine ⟨181948142735782325032807637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121298761823854883355205091 181948142735782325032807637)
                    ·
                      refine ⟨4264409595369898242956429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181948142735782325032807637 4264409595369898242956429)
                      ·
                        rfl

theorem cell23_8304908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_8304908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8304908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8304908 prefixEnd_8304908 := by exact prefixLift 8304908
  have htrace : WordTrace (prefixWord ++ tailWord_8304908) baseStart_8304908 baseEnd_8304908 := by
    simpa [prefixWord, tailWord_8304908, baseEnd_8304908] using wordTrace_append hprefix tailTrace_8304908
  have hstable : (prefixWord ++ tailWord_8304908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8304908).length < 2 ^ (prefixWord ++ tailWord_8304908).sum := by decide
  have hdescent : baseEnd_8304908 < baseStart_8304908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8304908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
